import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.GroupDetAlt

noncomputable section

namespace UpperTheory.Gal.Gen

/- English proof (translation)
Introduce `X _ B V hV`. Set `L` to `WithLp.linearEquiv 2 ℂ (X → ℂ)`. Set `V' : Submodule ℂ (EuclideanSpace ℂ X)` to `V.map (L.symm : (X → ℂ) →ₗ[ℂ] EuclideanSpace ℂ X)`. Establish `hfr : Module.finrank ℂ V' = Module.finrank ℂ V` using `LinearEquiv.finrank_map_eq L.symm V`. Set `e` to `stdOrthonormalBasis ℂ V'`.

Set `f : Fin (Module.finrank ℂ V') → EuclideanSpace ℂ X` to `fun i => (e i : EuclideanSpace ℂ X)`. Apply the tactic sequence `have hf : Orthonormal ℂ f := e.orthonormal.comp_linearIsometry V'.subtypeₗᵢ`. Establish `hfix : ∀ i x, ∑ y, B x y * f i y = f i x`. Introduce `i x`. Take `⟨v, hv, hvf⟩` from `(e i).2`.

Establish `h1 : ∀ y, f i y = v y`. Introduce `y`. Establish `: f i = L.symm v` using `hvf.symm`. Rewrite using `[this]`. Both sides reduce to the same expression.

Establish `h2` using `congrFun (hV v hv) x`. Simplify using `only [Matrix.mulVec, dotProduct] at h2`. Simplify using `only [h1]`. Conclude with `h2`. Set `r : X → EuclideanSpace ℂ X` to `fun x => WithLp.toLp 2 (fun y => starRingEnd ℂ (B x y))`.

Establish `hinner : ∀ i x, inner ℂ (r x) (f i) = f i x`. Introduce `i x`. Rewrite using `[← hfix i x, PiLp.inner_apply]`. Use `Finset.sum_congr rfl fun y _ => ?_` and prove the remaining obligations. Simplify using `[r, RCLike.inner_apply, mul_comm]`.

Establish `hbessel : ∀ x, ∑ i, ‖f i x‖ ^ 2 ≤ ∑ y, ‖B x y‖ ^ 2`. Introduce `x`. Establish `h` using `hf.sum_inner_products_le (x := r x) (s := Finset.univ)`. Establish `h3 : ‖r x‖ ^ 2 = ∑ y, ‖B x y‖ ^ 2`. Rewrite using `[EuclideanSpace.norm_sq_eq]`.

Simplify using `[r]`. Rewrite `h` using `[h3]`. Use `le_trans (le_of_eq ?_) h` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[norm_inner_symm, hinner]`.

Establish `hone : ∀ i, ∑ x, ‖f i x‖ ^ 2 = 1`. Introduce `i`. Rewrite using `[← EuclideanSpace.norm_sq_eq, hf.1 i]`. Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation.

Simplify using `[hone, hfr]`. Use `_ = ∑ x, ∑ i, ‖f i x‖ ^ 2 := Finset.sum_comm`. Use `_ ≤ ∑ x, ∑ y, ‖B x y‖ ^ 2 := Finset.sum_le_sum fun x _ => hbessel x`.
-/
theorem hS_pf : HS := by
  classical
  intro X _ B V hV
  let L := WithLp.linearEquiv 2 ℂ (X → ℂ)
  let V' : Submodule ℂ (EuclideanSpace ℂ X) := V.map (L.symm : (X → ℂ) →ₗ[ℂ] EuclideanSpace ℂ X)
  have hfr : Module.finrank ℂ V' = Module.finrank ℂ V := LinearEquiv.finrank_map_eq L.symm V
  let e := stdOrthonormalBasis ℂ V'
  let f : Fin (Module.finrank ℂ V') → EuclideanSpace ℂ X := fun i => (e i : EuclideanSpace ℂ X)
  have hf : Orthonormal ℂ f := e.orthonormal.comp_linearIsometry V'.subtypeₗᵢ
  have hfix : ∀ i x, ∑ y, B x y * f i y = f i x := by
    intro i x
    obtain ⟨v, hv, hvf⟩ := (e i).2
    have h1 : ∀ y, f i y = v y := by
      intro y
      have : f i = L.symm v := hvf.symm
      rw [this]
      rfl
    have h2 := congrFun (hV v hv) x
    simp only [Matrix.mulVec, dotProduct] at h2
    simp only [h1]
    exact h2
  let r : X → EuclideanSpace ℂ X := fun x => WithLp.toLp 2 (fun y => starRingEnd ℂ (B x y))
  have hinner : ∀ i x, inner ℂ (r x) (f i) = f i x := by
    intro i x
    rw [← hfix i x, PiLp.inner_apply]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp [r, RCLike.inner_apply, mul_comm]
  have hbessel : ∀ x, ∑ i, ‖f i x‖ ^ 2 ≤ ∑ y, ‖B x y‖ ^ 2 := by
    intro x
    have h := hf.sum_inner_products_le (x := r x) (s := Finset.univ)
    have h3 : ‖r x‖ ^ 2 = ∑ y, ‖B x y‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [r]
    rw [h3] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [norm_inner_symm, hinner]
  have hone : ∀ i, ∑ x, ‖f i x‖ ^ 2 = 1 := by
    intro i
    rw [← EuclideanSpace.norm_sq_eq, hf.1 i]
    simp
  calc (Module.finrank ℂ V : ℝ) = ∑ i : Fin (Module.finrank ℂ V'), ∑ x, ‖f i x‖ ^ 2 := by
        simp [hone, hfr]
    _ = ∑ x, ∑ i, ‖f i x‖ ^ 2 := Finset.sum_comm
    _ ≤ ∑ x, ∑ y, ‖B x y‖ ^ 2 := Finset.sum_le_sum fun x _ => hbessel x

end UpperTheory.Gal.Gen

end
