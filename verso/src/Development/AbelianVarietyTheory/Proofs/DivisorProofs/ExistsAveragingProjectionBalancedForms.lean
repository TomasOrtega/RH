import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc

namespace GlobalTheory.Poinc

/- English proof (translation)
Introduce `O _ bar X _ _ n c b T hc hT hint hsum hpos`. Set `f : Fin n → X →ₗ[ℤ] X` to `fun s => DistribMulAction.toLinearMap ℤ X (b s)`. Set `P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X` to `{ toFun := fun β => ∑ s, ∑ t, T s t • β.compl₁₂ (f s) (f t) map_add' := fun β γ => by`. Use extensionality with `x y`. Simplify using `[Finset.sum_add_distrib, mul_add]`.

Use the proof step `map_smul' := fun m β => by`. Use extensionality with `x y`. Simplify using `[Finset.mul_sum, mul_left_comm] }`. Establish `hP : ∀ β x y, P β x y = ∑ s, ∑ t, T s t * β (b s • x) (b t • y)`. Introduce `β x y`.

Simplify using `[P, f, LinearMap.sum_apply]`. Both sides reduce to the same expression. Set `sp : X → O →ₗ[ℤ] X` to `fun y => (LinearMap.toSpanSingleton O X y).restrictScalars ℤ`. Establish `hsp : ∀ y u, sp y u = u • y` using `fun y u => rfl`. Establish `hsumL : ∀ L : O →ₗ[ℤ] ℤ, ∑ s, ∑ t, T s t * L (bar (b s) * b t) = c * L 1`.

Introduce `L`. Use `congrArg L hsum` as an intermediate fact. Simplify using `only [map_sum, map_zsmul, smul_eq_mul] at this`. Rewrite using `[this]`. Establish `hc1 : (c : O) = c • (1 : O)` using `(nsmul_one c).symm`.

Rewrite using `[hc1, map_nsmul, nsmul_eq_mul]`. Use `⟨P, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `β hβ`. Establish `key : (∀ y z, P β y z = P β z y) ∧ ∀ (a : O) y z, P β (a • y) z = P β y (bar a • z)`. Prove the components needed by the constructor for the conclusion.

Introduce `x y`. Rewrite using `[hP, hP, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Rewrite using `[hT, hβ]`. Introduce `a x y`.

Rewrite using `[hP, hP]`. Use `hint a (β.compl₁₂ (sp x) (sp y))` as an intermediate fact. Simplify using `only [LinearMap.compl₁₂_apply, hsp, mul_smul] at this`. Conclude with `this`. Conclude with `key`.

Introduce `β hβ`. Take `⟨h1, h2⟩` from `hβ`. Use extensionality with `x y`. Rewrite using `[hP]`. Establish `e : ∀ s t, β (b s • x) (b t • y) = (β x ∘ₗ sp y) (bar (b s) * b t)`.

Introduce `s t`. Rewrite using `[h2]`. Simplify using `[hsp, mul_smul]`. Simplify using `only [e]`. Rewrite using `[hsumL]`.

Simplify using `[hsp]`. Introduce `l hl`. Establish `hQ : ∀ x, P (GlobalTheory.PolFan.sqForm l) x x = ∑ s, ∑ t, T s t * (fun s => l (b s • x)) s * (fun s => l (b s • x)) t`. Introduce `x`. Rewrite using `[hP]`.

Simplify using `[GlobalTheory.PolFan.sqForm_apply, mul_assoc]`. Establish `hnn : ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x`. Introduce `x`. Rewrite using `[hQ]`. Distinguish the cases in `hv : (fun s => l (b s • x)) = 0`.

Rewrite using `[hv]`. Simplify using the standard rewrite rules. Conclude with `(hpos _ hv).le`. Use `⟨fun h0 => ?_, hnn⟩` and prove the remaining obligations. Establish `hv : ∀ y t, l (b t • y) = 0`.

Introduce `y t`. Assume the negation of the conclusion as `hne`. Establish `hv : (fun s => l (b s • y)) ≠ 0` using `fun h => hne (congrFun h t)`. Use `hpos _ hv` as an intermediate fact. Rewrite `this` using `[← hQ, h0]`.

Simplify using `at this`. Choose the witnesses or unpack the hypotheses as in `⟨x, hx⟩ : ∃ x, l x ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hl (LinearMap.ext h)`.

Use `hsumL (l ∘ₗ sp x)` as an intermediate fact. Establish `hz : ∀ s t, (l ∘ₗ sp x) (bar (b s) * b t) = 0`. Introduce `s t`. Simplify using `only [LinearMap.comp_apply, hsp]`. Rewrite using `[mul_comm, mul_smul]`.

Conclude with `hv _ _`. Simplify using `only [hz, mul_zero, Finset.sum_const_zero] at this`. Simplify using `[hsp] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_avg_proj_balForms : ∀ (O : Type) [CommRing O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X] (n c : ℕ) (b : Fin n → O) (T : Matrix (Fin n) (Fin n) ℤ), 0 < c → (∀ s t, T s t = T t s) → (∀ (a : O) (g : O →ₗ[ℤ] O →ₗ[ℤ] ℤ), ∑ s, ∑ t, T s t * g (b s * a) (b t) = ∑ s, ∑ t, T s t * g (b s) (b t * bar a)) → ∑ s, ∑ t, T s t • (bar (b s) * b t) = (c : O) → (∀ v : Fin n → ℤ, v ≠ 0 → 0 < ∑ s, ∑ t, T s t * v s * v t) → ∃ P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X, (∀ β : LinearMap.BilinForm ℤ X, (∀ x y, β x y = β y x) → P β ∈ GlobalTheory.PolFan.balForms bar X) ∧ (∀ β ∈ GlobalTheory.PolFan.balForms bar X, P β = (c : ℤ) • β) ∧ ∀ l : X →ₗ[ℤ] ℤ, l ≠ 0 → P (GlobalTheory.PolFan.sqForm l) ≠ 0 ∧ ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x := by
  intro O _ bar X _ _ n c b T hc hT hint hsum hpos
  let f : Fin n → X →ₗ[ℤ] X := fun s => DistribMulAction.toLinearMap ℤ X (b s)
  let P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X :=
    { toFun := fun β => ∑ s, ∑ t, T s t • β.compl₁₂ (f s) (f t)
      map_add' := fun β γ => by
        ext x y
        simp [Finset.sum_add_distrib, mul_add]
      map_smul' := fun m β => by
        ext x y
        simp [Finset.mul_sum, mul_left_comm] }
  have hP : ∀ β x y, P β x y = ∑ s, ∑ t, T s t * β (b s • x) (b t • y) := by
    intro β x y
    simp [P, f, LinearMap.sum_apply]
    rfl

  let sp : X → O →ₗ[ℤ] X := fun y => (LinearMap.toSpanSingleton O X y).restrictScalars ℤ
  have hsp : ∀ y u, sp y u = u • y := fun y u => rfl
  have hsumL : ∀ L : O →ₗ[ℤ] ℤ, ∑ s, ∑ t, T s t * L (bar (b s) * b t) = c * L 1 := by
    intro L
    have := congrArg L hsum
    simp only [map_sum, map_zsmul, smul_eq_mul] at this
    rw [this]
    have hc1 : (c : O) = c • (1 : O) := (nsmul_one c).symm
    rw [hc1, map_nsmul, nsmul_eq_mul]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro β hβ
    have key : (∀ y z, P β y z = P β z y) ∧ ∀ (a : O) y z, P β (a • y) z = P β y (bar a • z) := by
      constructor
      · intro x y
        rw [hP, hP, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
        rw [hT, hβ]
      · intro a x y
        rw [hP, hP]
        have := hint a (β.compl₁₂ (sp x) (sp y))
        simp only [LinearMap.compl₁₂_apply, hsp, mul_smul] at this
        exact this
    exact key
  · intro β hβ
    obtain ⟨h1, h2⟩ := hβ
    ext x y
    rw [hP]
    have e : ∀ s t, β (b s • x) (b t • y) = (β x ∘ₗ sp y) (bar (b s) * b t) := by
      intro s t
      rw [h2]
      simp [hsp, mul_smul]
    simp only [e]
    rw [hsumL]
    simp [hsp]
  · intro l hl
    have hQ : ∀ x, P (GlobalTheory.PolFan.sqForm l) x x = ∑ s, ∑ t, T s t * (fun s => l (b s • x)) s * (fun s => l (b s • x)) t := by
      intro x
      rw [hP]
      simp [GlobalTheory.PolFan.sqForm_apply, mul_assoc]
    have hnn : ∀ x, 0 ≤ P (GlobalTheory.PolFan.sqForm l) x x := by
      intro x
      rw [hQ]
      by_cases hv : (fun s => l (b s • x)) = 0
      · rw [hv]; simp
      · exact (hpos _ hv).le
    refine ⟨fun h0 => ?_, hnn⟩
    have hv : ∀ y t, l (b t • y) = 0 := by
      intro y t
      by_contra hne
      have hv : (fun s => l (b s • y)) ≠ 0 := fun h => hne (congrFun h t)
      have := hpos _ hv
      rw [← hQ, h0] at this
      simp at this
    obtain ⟨x, hx⟩ : ∃ x, l x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hl (LinearMap.ext h)
    have := hsumL (l ∘ₗ sp x)
    have hz : ∀ s t, (l ∘ₗ sp x) (bar (b s) * b t) = 0 := by
      intro s t
      simp only [LinearMap.comp_apply, hsp]
      rw [mul_comm, mul_smul]
      exact hv _ _
    simp only [hz, mul_zero, Finset.sum_const_zero] at this
    simp [hsp] at this
    omega

end GlobalTheory.Poinc
