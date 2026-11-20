import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.EpsteinZeta.DedekindFactorK

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5

open NumberField Classical
open scoped Pointwise

/- English proof (translation)
Rewrite using `[AddSubgroup.mem_smul_pointwise_iff_exists]`. Simplify using `only [smul_eq_mul]`.
-/
theorem mem_smul_iff' (Λ : AddSubgroup ℂ) (c : ℂ) (w : ℂ) :
    w ∈ c • Λ ↔ ∃ x ∈ Λ, c * x = w := by
  rw [AddSubgroup.mem_smul_pointwise_iff_exists]
  simp only [smul_eq_mul]

def smulEquivNZ (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) :
    {w : ℂ // w ∈ Λ ∧ w ≠ 0} ≃ {w : ℂ // w ∈ c • Λ ∧ w ≠ 0} where
  toFun w := ⟨c * w.1, (mem_smul_iff' Λ c _).2 ⟨w.1, w.2.1, rfl⟩, mul_ne_zero hc w.2.2⟩
  invFun w := ⟨c⁻¹ * w.1, by
    obtain ⟨x, hx, hxw⟩ := (mem_smul_iff' Λ c _).1 w.2.1
    refine ⟨?_, mul_ne_zero (inv_ne_zero hc) w.2.2⟩
    rw [← hxw, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]; exact hx⟩
  left_inv w := by ext; simp [hc]
  right_inv w := by ext; simp [hc]

/- English proof (translation)
Unfold `eisG`. Rewrite using `[show (∑' w : {w : ℂ // w ∈ c • Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)) = ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / ((smulEquivNZ Λ c hc w : ℂ)) ^ (2 * k) from ((smulEquivNZ Λ c hc).tsum_eq (fun w => 1 / (w : ℂ) ^ (2 * k))).symm]`. Rewrite using `[← tsum_mul_left]`. Use `congr 1`. Use function extensionality and compare the values at `w`.

Use `show 1 / (c * w.1) ^ (2 * k) = (c ^ (2 * k))⁻¹ * (1 / w.1 ^ (2 * k))`. Rewrite using `[one_div, one_div, mul_pow, mul_inv]`.
-/
theorem eisG_smul (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) (k : ℕ) :
    eisG (c • Λ) k = (c ^ (2 * k))⁻¹ * eisG Λ k := by
  unfold eisG
  rw [show (∑' w : {w : ℂ // w ∈ c • Λ ∧ w ≠ 0}, 1 / (w : ℂ) ^ (2 * k)) =
      ∑' w : {w : ℂ // w ∈ Λ ∧ w ≠ 0}, 1 / ((smulEquivNZ Λ c hc w : ℂ)) ^ (2 * k) from
      ((smulEquivNZ Λ c hc).tsum_eq (fun w => 1 / (w : ℂ) ^ (2 * k))).symm]
  rw [← tsum_mul_left]
  congr 1
  funext w
  show 1 / (c * w.1) ^ (2 * k) = (c ^ (2 * k))⁻¹ * (1 / w.1 ^ (2 * k))
  rw [one_div, one_div, mul_pow, mul_inv]

/- English proof (translation)
Use `first`. Consider the case `(unfold discr; simp only [g2, g3, eisG_smul Λ c hc]; ring)`. Consider the case `(unfold discr g2 g3; done)`.
-/
theorem discr_smul (Λ : AddSubgroup ℂ) (c : ℂ) (hc : c ≠ 0) :
    discr (c • Λ) = (c ^ 12)⁻¹ * discr Λ := by
  first
  | (unfold discr; simp only [g2, g3, eisG_smul Λ c hc]; ring)
  | (unfold discr g2 g3; done)

/- English proof (translation)
Unfold `latI`. Rewrite using `[AddSubgroup.pointwise_smul_def]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `w ⟨c, hc, rfl⟩`.

Conclude with `AddSubgroup.mem_map.2 ⟨φ c, AddSubgroup.subset_closure ⟨c, hc, (one_mul _).symm⟩, rfl⟩`. Use `AddSubgroup.map_le_iff_le_comap.2 ?_` and prove the remaining obligations. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `x ⟨c, hc, rfl⟩`. Conclude with `AddSubgroup.subset_closure ⟨c, hc, show δ * (1 * φ c) = δ * φ c by rw [one_mul]⟩`.
-/
theorem latI_eq_smul {K : Type} [Field K] [NumberField K] (φ : K →+* ℂ) (𝔞 : Ideal (𝓞 K))
    (δ : ℂ) : latI φ 𝔞 δ = δ • latI φ 𝔞 1 := by
  unfold latI
  rw [AddSubgroup.pointwise_smul_def]
  apply le_antisymm
  · rw [AddSubgroup.closure_le]
    rintro w ⟨c, hc, rfl⟩
    exact AddSubgroup.mem_map.2 ⟨φ c, AddSubgroup.subset_closure ⟨c, hc, (one_mul _).symm⟩, rfl⟩
  · refine AddSubgroup.map_le_iff_le_comap.2 ?_
    refine (AddSubgroup.closure_le _).2 ?_
    rintro x ⟨c, hc, rfl⟩
    exact AddSubgroup.subset_closure ⟨c, hc, show δ * (1 * φ c) = δ * φ c by rw [one_mul]⟩

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5
