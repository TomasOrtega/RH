import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfMulUnimodular

open scoped Matrix Topology

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

/- English proof (translation)
Use `set K : Set (Fin n → ℂ) := (S : Set (Fin n → ℂ)) ∩ Metric.sphere 0 1 with hK`. Establish `hKc : IsCompact K` using `(isCompact_sphere 0 1).inter_left S.closed_of_finiteDimensional`. Set `F : Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → ℝ` to `fun Z w => ε * (star w ⬝ᵥ Z.mulVec w).re`. Establish `hF : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) => F p.1 p.2)` using `continuous_const.mul (Complex.continuous_re.comp ((continuous_snd.star).dotProduct (continuous_fst.matrix_mulVec continuous_snd)))`. Establish `hscale : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (c : ℝ), F Z ((c : ℂ) • w) = c ^ 2 * F Z w`.

Introduce `Z w c`. Simplify using `only [F, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul, Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `heq : {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} = {Z | ∀ w ∈ K, 0 < F Z w}`. Use extensionality with `Z`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `hZ w ⟨hwS, hw1⟩`. Use `hZ w hwS ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `at hw1`.

Introduce `hZ w hwS hw0`. Establish `hn : 0 < ‖w‖` using `norm_pos_iff.mpr hw0`. Establish `hmem : ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ K`. Use `⟨S.smul_mem _ hwS, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']`.

Establish `h2` using `hZ _ hmem`. Rewrite `h2` using `[hscale]`. Conclude with `pos_of_mul_pos_right h2 (by positivity)`. Rewrite using `[heq, isOpen_iff_mem_nhds]`. Introduce `Z₀ hZ₀`.

Conclude with `hKc.eventually_forall_of_forall_eventually fun w hw => (hF.tendsto (Z₀, w)).eventually (lt_mem_nhds (hZ₀ w hw))`.
-/
theorem isOpen_posOn (n : ℕ) (ε : ℝ) (S : Submodule ℂ (Fin n → ℂ)) :
    IsOpen {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} := by
  set K : Set (Fin n → ℂ) := (S : Set (Fin n → ℂ)) ∩ Metric.sphere 0 1 with hK
  have hKc : IsCompact K := (isCompact_sphere 0 1).inter_left S.closed_of_finiteDimensional
  let F : Matrix (Fin n) (Fin n) ℂ → (Fin n → ℂ) → ℝ := fun Z w => ε * (star w ⬝ᵥ Z.mulVec w).re
  have hF : Continuous (fun p : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) => F p.1 p.2) :=
    continuous_const.mul (Complex.continuous_re.comp
      ((continuous_snd.star).dotProduct (continuous_fst.matrix_mulVec continuous_snd)))
  have hscale : ∀ (Z : Matrix (Fin n) (Fin n) ℂ) (w : Fin n → ℂ) (c : ℝ),
      F Z ((c : ℂ) • w) = c ^ 2 * F Z w := by
    intro Z w c
    simp only [F, Matrix.mulVec_smul, dotProduct_smul, star_smul, smul_dotProduct, smul_eq_mul,
      Complex.star_def, Complex.conj_ofReal, Complex.re_ofReal_mul]
    ring
  have heq : {Z : Matrix (Fin n) (Fin n) ℂ | PosOn ε Z S} = {Z | ∀ w ∈ K, 0 < F Z w} := by
    ext Z
    constructor
    · rintro hZ w ⟨hwS, hw1⟩
      refine hZ w hwS ?_
      rintro rfl
      simp at hw1
    · intro hZ w hwS hw0
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
      have hmem : ((‖w‖⁻¹ : ℝ) : ℂ) • w ∈ K := by
        refine ⟨S.smul_mem _ hwS, ?_⟩
        rw [mem_sphere_zero_iff_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_inv, abs_norm, inv_mul_cancel₀ hn.ne']
      have h2 := hZ _ hmem
      rw [hscale] at h2
      exact pos_of_mul_pos_right h2 (by positivity)
  rw [heq, isOpen_iff_mem_nhds]
  intro Z₀ hZ₀
  exact hKc.eventually_forall_of_forall_eventually fun w hw =>
    (hF.tendsto (Z₀, w)).eventually (lt_mem_nhds (hZ₀ w hw))

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
