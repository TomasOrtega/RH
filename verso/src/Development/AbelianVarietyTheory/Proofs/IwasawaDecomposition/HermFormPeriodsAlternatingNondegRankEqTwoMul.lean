import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanPeriodLatticeComplexSemiAbelianEqTopStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
Simplify using `only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `hH.apply i j` as an intermediate fact. Rewrite using `[← this]`.

Simplify using `only [star_star, Pi.star_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hermForm_conj_symm_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hH.apply i j
  rw [← this]
  simp only [star_star, Pi.star_apply]
  ring

noncomputable def hermFormImBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

/- English proof (translation)
Introduce `g r x M Hm hli hsp hH hpos hM`. Establish `hanti : Mᵀ = -M`. Use extensionality with `i j`. Simplify using `only [Matrix.transpose_apply, Matrix.neg_apply, ← hM]`. Rewrite using `[hermForm_conj_symm_of_isHermitian Hm hH]`.

Simplify using the standard rewrite rules. Use `⟨hanti, ?_, ?_⟩` and prove the remaining obligations. Introduce `hdet`. Take `⟨v, hv0, hv⟩` from `Matrix.exists_mulVec_eq_zero_iff.mpr hdet`. Use `set z : Fin g → ℂ := ∑ j, v j • x j with hz`.

Establish `hz0 : z ≠ 0`. Introduce `h0`. Apply `hv0` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Conclude with `Fintype.linearIndependent_iff.mp hli v h0 j`.

Establish `hxi : ∀ i, hermFormImBilin Hm (x i) z = 0`. Introduce `i`. Establish `: hermFormImBilin Hm (x i) z = ∑ j, v j * M i j`. Rewrite using `[hz, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, smul_eq_mul, ← hM i j]`. Both sides reduce to the same expression. Rewrite using `[this]`. Use `congrFun hv i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, mul_comm]`.

Establish `hall : ∀ y, hermFormImBilin Hm y z = 0`. Establish `hle : Submodule.span ℝ (Set.range x) ≤ LinearMap.ker ((hermFormImBilin Hm).flip z)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `using hxi i`.

Introduce `y`. Establish `hy : y ∈ Submodule.span ℝ (Set.range x)` using `by rw [hsp]; trivial`. Simplify using `using hle hy`. Establish `h1` using `hall (Complex.I • z)`. Establish `h2 : hermFormImBilin Hm (Complex.I • z) z = (hermForm Hm z z).re` using `by show (hermForm Hm (Complex.I • z) z).im = _`.

Simplify using `[hermForm, smul_dotProduct]`. Use `hpos z hz0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `finrank_span_eq_card hli`. Rewrite `h1` using `[hsp, finrank_top, Module.finrank_pi_fintype]`.

Simplify using `[Complex.finrank_real_complex] at h1`. Use linear arithmetic over natural numbers and integers.
-/
theorem hermForm_periods_alternating_nondeg :
    ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), LinearIndependent ℝ x → Submodule.span ℝ (Set.range x) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → Mᵀ = -M ∧ M.det ≠ 0 ∧ r = 2 * g := by
  intro g r x M Hm hli hsp hH hpos hM
  have hanti : Mᵀ = -M := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, ← hM]
    rw [hermForm_conj_symm_of_isHermitian Hm hH]
    simp
  refine ⟨hanti, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set z : Fin g → ℂ := ∑ j, v j • x j with hz
    have hz0 : z ≠ 0 := by
      intro h0
      apply hv0
      funext j
      exact Fintype.linearIndependent_iff.mp hli v h0 j
    have hxi : ∀ i, hermFormImBilin Hm (x i) z = 0 := by
      intro i
      have : hermFormImBilin Hm (x i) z = ∑ j, v j * M i j := by
        rw [hz, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, ← hM i j]
        rfl
      rw [this]
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    have hall : ∀ y, hermFormImBilin Hm y z = 0 := by
      have hle : Submodule.span ℝ (Set.range x) ≤ LinearMap.ker ((hermFormImBilin Hm).flip z) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simpa using hxi i
      intro y
      have hy : y ∈ Submodule.span ℝ (Set.range x) := by rw [hsp]; trivial
      simpa using hle hy
    have h1 := hall (Complex.I • z)
    have h2 : hermFormImBilin Hm (Complex.I • z) z = (hermForm Hm z z).re := by
      show (hermForm Hm (Complex.I • z) z).im = _
      simp [hermForm, smul_dotProduct]
    have := hpos z hz0
    linarith
  · have h1 := finrank_span_eq_card hli
    rw [hsp, finrank_top, Module.finrank_pi_fintype] at h1
    simp [Complex.finrank_real_complex] at h1
    omega

end GlobalTheory
