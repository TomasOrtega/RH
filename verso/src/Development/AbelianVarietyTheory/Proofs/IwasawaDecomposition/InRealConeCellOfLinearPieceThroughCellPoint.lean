import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfToRealRel
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

noncomputable section

namespace GlobalTheory.PolFan

/- English proof (translation)
Establish `hev : ∀ {p : ℕ} (δ : Fin p → LinearMap.BilinForm ℤ X) (c : Fin p → ℝ), (∀ j, 0 ≤ c j) → φ.LinearOn δ → toReal β = ∑ j, c j • toReal (δ j) → φ.evalZ β = ∑ j, c j * φ.evalZ (δ j)`. Introduce `p δ c hc hl e`. Rewrite using `[← hl c hc]`. Unfold `InvFun.evalZ`. Use `congr 1`.

Use function extensionality and compare the values at `x y`. Simplify `LinearMap.congr_fun₂ e x y` using `[LinearMap.sum_apply]`. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `hγ.strict`. Establish `ea` using `hev γ a ha hγ.linear e1`. Establish `eb` using `hev γ' b (fun i => (hb i).le) hlin e2`.

Establish `la` using `apply_eq_of_toReal_eq e1 ℓ`. Establish `lb` using `apply_eq_of_toReal_eq e2 ℓ`. Establish `hsum : ∑ i, b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) = 0`. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[← lb, sub_eq_zero, la]`.

Establish `e3 : ∑ i, b i * ((N : ℝ) * φ.evalZ (γ' i)) = N * φ.evalZ β`. Rewrite using `[eb, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[e3, ea, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [h1 j]; ring`. Establish `hnn : ∀ i, 0 ≤ b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i))` using `fun i => mul_nonneg (hb i).le (sub_nonneg.2 (h2 _ (hmem i) (hpos i)))`.

Establish `hz` using `(Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hsum i (Finset.mem_univ _)`. Establish `heq : (N : ℝ) * φ.evalZ (γ' i) = ℓ (γ' i)`. Use `(mul_eq_zero.1 hz).resolve_left (hb i).ne'` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨kk, c, hk, hc⟩` from `h3 _ (hmem i) (hpos i) heq`.

Establish `hkR : (kk : ℝ) ≠ 0` using `by exact_mod_cast hk.ne'`. Use `⟨fun j => (c j : ℝ) / kk, fun j => by positivity, LinearMap.ext₂ fun x y => ?_⟩` and prove the remaining obligations. Establish `h4` using `LinearMap.congr_fun₂ hc x y`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h4`. Establish `h5 : (kk : ℝ) * (γ' i x y : ℝ) = ∑ j, (c j : ℝ) * (γ j x y : ℝ)` using `by exact_mod_cast h4`.

Simplify using `only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Establish `h6 : (γ' i x y : ℝ) = (∑ j, (c j : ℝ) * (γ j x y : ℝ)) / kk`. Rewrite using `[eq_div_iff hkR, ← h5]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h6, Finset.sum_div]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`.
-/
theorem inRCone_of_interior_linearOn {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X]
    [Module O X] [Module.Finite O X] {m k : ℕ}
    (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X) (hγ : IsCell bar φ γ)
    (hmem : ∀ i, γ' i ∈ balForms bar X) (hpos : ∀ i y, 0 ≤ γ' i y y) (hlin : φ.LinearOn γ')
    (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ i, 0 < b i)
    (e1 : toReal β = ∑ j, a j • toReal (γ j)) (e2 : toReal β = ∑ i, b i • toReal (γ' i)) (i : Fin k) :
    InRCone γ (γ' i) := by
  have hev : ∀ {p : ℕ} (δ : Fin p → LinearMap.BilinForm ℤ X) (c : Fin p → ℝ), (∀ j, 0 ≤ c j) → φ.LinearOn δ →
      toReal β = ∑ j, c j • toReal (δ j) → φ.evalZ β = ∑ j, c j * φ.evalZ (δ j) := by
    intro p δ c hc hl e
    rw [← hl c hc]
    unfold InvFun.evalZ
    congr 1
    funext x y
    simpa [LinearMap.sum_apply] using LinearMap.congr_fun₂ e x y
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have ea := hev γ a ha hγ.linear e1
  have eb := hev γ' b (fun i => (hb i).le) hlin e2
  have la := apply_eq_of_toReal_eq e1 ℓ
  have lb := apply_eq_of_toReal_eq e2 ℓ
  have hsum : ∑ i, b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← lb, sub_eq_zero, la]
    have e3 : ∑ i, b i * ((N : ℝ) * φ.evalZ (γ' i)) = N * φ.evalZ β := by
      rw [eb, Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e3, ea, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [h1 j]; ring
  have hnn : ∀ i, 0 ≤ b i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) := fun i =>
    mul_nonneg (hb i).le (sub_nonneg.2 (h2 _ (hmem i) (hpos i)))
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)).1 hsum i (Finset.mem_univ _)
  have heq : (N : ℝ) * φ.evalZ (γ' i) = ℓ (γ' i) := by
    have := (mul_eq_zero.1 hz).resolve_left (hb i).ne'
    linarith
  obtain ⟨kk, c, hk, hc⟩ := h3 _ (hmem i) (hpos i) heq
  have hkR : (kk : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  refine ⟨fun j => (c j : ℝ) / kk, fun j => by positivity, LinearMap.ext₂ fun x y => ?_⟩
  have h4 := LinearMap.congr_fun₂ hc x y
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul] at h4
  have h5 : (kk : ℝ) * (γ' i x y : ℝ) = ∑ j, (c j : ℝ) * (γ j x y : ℝ) := by exact_mod_cast h4
  simp only [toReal_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have h6 : (γ' i x y : ℝ) = (∑ j, (c j : ℝ) * (γ j x y : ℝ)) / kk := by
    rw [eq_div_iff hkR, ← h5]; ring
  rw [h6, Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring

/- English proof (translation)
Introduce `O _ bar φ X _ _ _ m k γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i`. Conclude with `inRCone_of_interior_linearOn bar φ γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i`.
-/
theorem inRCone_of_interior_linearOn' : ∀ {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] {m k : ℕ}
  (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin k → LinearMap.BilinForm ℤ X), IsCell bar φ γ → (∀ i, γ' i ∈ balForms bar X) →
  (∀ i y, 0 ≤ γ' i y y) → φ.LinearOn γ' →
  ∀ (β : LinearMap.BilinForm ℤ X) (a : Fin m → ℝ) (b : Fin k → ℝ), (∀ j, 0 ≤ a j) → (∀ i, 0 < b i) →
    toReal β = ∑ j, a j • toReal (γ j) → toReal β = ∑ i, b i • toReal (γ' i) → ∀ i, InRCone γ (γ' i) :=
by
  intro O _ bar φ X _ _ _ m k γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i
  exact inRCone_of_interior_linearOn bar φ γ γ' hγ hmem hpos hlin β a b ha hb e1 e2 i

end GlobalTheory.PolFan
