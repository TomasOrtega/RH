import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan

/- English proof (translation)
Take `⟨c, hc, e⟩` from `hβ`. Rewrite using `[apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff φ G).1 hlin c hc, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring`.
-/
theorem apply_eq_of_inRCone_cell {O : Type} [CommRing O] {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
    [Module.Finite O X] {m : ℕ} {G : Fin m → LinearMap.BilinForm ℤ X} (hlin : φ.LinearOn G) {N : ℕ}
    {ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ} (h1 : ∀ i, (ℓ (G i) : ℝ) = N * φ.evalZ (G i))
    {β : LinearMap.BilinForm ℤ X} (hβ : InRCone G β) : (ℓ β : ℝ) = N * φ.evalZ β := by
  obtain ⟨c, hc, e⟩ := hβ
  rw [apply_eq_of_toReal_eq e ℓ, ← evalR_toReal, e, (linearOn_iff φ G).1 hlin c hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [h1 i]; ring

/- English proof (translation)
Establish `hk' : (k : ℝ) ≠ 0` using `by exact_mod_cast hk.ne'`. Use `⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩` and prove the remaining obligations. Establish `h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * δ i a b`. Simplify `LinearMap.congr_fun₂ h a b` using `[LinearMap.sum_apply]`. Establish `h2 : (k : ℝ) * (β a b : ℝ) = ∑ i, (c i : ℝ) * (δ i a b : ℝ)` using `by exact_mod_cast h1`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]`. Rewrite using `[show (β a b : ℝ) = (∑ i, (c i : ℝ) * (δ i a b : ℝ)) / k from by rw [← h2]; field_simp, Finset.sum_div]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem inRCone_of_nat_rel {X : Type} [AddCommGroup X] {n : ℕ} {δ : Fin n → LinearMap.BilinForm ℤ X}
    {β : LinearMap.BilinForm ℤ X} {k : ℕ} {c : Fin n → ℕ} (hk : 0 < k) (h : k • β = ∑ i, c i • δ i) : InRCone δ β := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun i => (c i : ℝ) / k, fun i => by positivity, LinearMap.ext₂ fun a b => ?_⟩
  have h1 : (k : ℤ) * β a b = ∑ i, (c i : ℤ) * δ i a b := by
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ h a b
  have h2 : (k : ℝ) * (β a b : ℝ) = ∑ i, (c i : ℝ) * (δ i a b : ℝ) := by exact_mod_cast h1
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, toReal_apply, smul_eq_mul]
  rw [show (β a b : ℝ) = (∑ i, (c i : ℝ) * (δ i a b : ℝ)) / k from by rw [← h2]; field_simp, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Introduce `O _ bar φ X _ _ _ m n G δ hG hδ hin`. Take `⟨NG, ℓG, hNG, g1, -, -⟩` from `hG.strict`. Take `⟨Nδ, ℓδ, hNδ, d1, d2, d3⟩` from `hδ.strict`. Establish `hNG' : (0 : ℝ) < NG` using `by exact_mod_cast hNG`. Establish `key : ∀ β : LinearMap.BilinForm ℤ X, InRCone G β → (ℓG β : ℝ) = NG * φ.evalZ β` using `fun β hβ => apply_eq_of_inRCone_cell hG.linear g1 hβ`.

Establish `hval : ∀ β : LinearMap.BilinForm ℤ X, (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) β : ℤ)) : ℝ) = NG * ℓδ β - Nδ * ℓG β` using `fun β => by simp`. Use `⟨(NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG, fun j => ?_, fun k => ?_, fun β hβ hp hc h0 => ?_⟩` and prove the remaining obligations. Establish `h1 : (0 : ℝ) ≤ (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (G j) : ℤ)) : ℝ)`. Rewrite using `[hval, g1 j]`. Use `d2 (G j) (hG.mem j) (hG.nonneg j)` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `h1` after adjusting the coercions. Establish `h1 : (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (δ k) : ℤ)) : ℝ) = 0`. Rewrite using `[hval, key _ (hin k), d1 k]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `h1` after adjusting the coercions. Establish `h1` using `hval β`. Rewrite `h1` using `[h0, key β hc]`. Establish `h2 : (Nδ : ℝ) * φ.evalZ β = ℓδ β`. Establish `: (NG : ℝ) * ((Nδ : ℝ) * φ.evalZ β - ℓδ β) = 0` using `by push_cast at h1; linarith`.

Use `(mul_eq_zero.1 this).resolve_left hNG'.ne'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨k, c, hk, e⟩` from `d3 β hβ hp h2`. Conclude with `inRCone_of_nat_rel hk e`.
-/
theorem exists_cut_of_cell_le : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] (m n : ℕ) (G : Fin m → LinearMap.BilinForm ℤ X) (δ : Fin n → LinearMap.BilinForm ℤ X),
    IsCell bar φ G → IsCell bar φ δ → (∀ k, InRCone G (δ k)) → ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ,
      (∀ j, 0 ≤ h (G j)) ∧ (∀ k, h (δ k) = 0) ∧
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone G β → h β = 0 → InRCone δ β := by
  intro O _ bar φ X _ _ _ m n G δ hG hδ hin
  obtain ⟨NG, ℓG, hNG, g1, -, -⟩ := hG.strict
  obtain ⟨Nδ, ℓδ, hNδ, d1, d2, d3⟩ := hδ.strict
  have hNG' : (0 : ℝ) < NG := by exact_mod_cast hNG
  have key : ∀ β : LinearMap.BilinForm ℤ X, InRCone G β → (ℓG β : ℝ) = NG * φ.evalZ β :=
    fun β hβ => apply_eq_of_inRCone_cell hG.linear g1 hβ
  have hval : ∀ β : LinearMap.BilinForm ℤ X, (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) β : ℤ)) : ℝ) = NG * ℓδ β - Nδ * ℓG β :=
    fun β => by simp
  refine ⟨(NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG, fun j => ?_, fun k => ?_, fun β hβ hp hc h0 => ?_⟩
  · have h1 : (0 : ℝ) ≤ (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (G j) : ℤ)) : ℝ) := by
      rw [hval, g1 j]
      have := d2 (G j) (hG.mem j) (hG.nonneg j)
      nlinarith
    exact_mod_cast h1
  · have h1 : (((((NG : ℤ) • ℓδ - (Nδ : ℤ) • ℓG) (δ k) : ℤ)) : ℝ) = 0 := by
      rw [hval, key _ (hin k), d1 k]; ring
    exact_mod_cast h1
  · have h1 := hval β
    rw [h0, key β hc] at h1
    have h2 : (Nδ : ℝ) * φ.evalZ β = ℓδ β := by
      have : (NG : ℝ) * ((Nδ : ℝ) * φ.evalZ β - ℓδ β) = 0 := by push_cast at h1; linarith
      have := (mul_eq_zero.1 this).resolve_left hNG'.ne'
      linarith
    obtain ⟨k, c, hk, e⟩ := d3 β hβ hp h2
    exact inRCone_of_nat_rel hk e

/- English proof (translation)
The claim follows from `exists_cut_of_cell_le`.
-/
example : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m n : ℕ) (G : Fin m → LinearMap.BilinForm ℤ X) (δ : Fin n → LinearMap.BilinForm ℤ X), IsCell bar φ G → IsCell bar φ δ → (∀ k, InRCone G (δ k)) → ∃ h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (∀ j, 0 ≤ h (G j)) ∧ (∀ k, h (δ k) = 0) ∧ ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone G β → h β = 0 → InRCone δ β := exists_cut_of_cell_le

end GlobalTheory.PolFan
