import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SchurOrthogonality.InstMeasurableSpaceMat

noncomputable section

namespace PI.WSF

open MvPolynomial Matrix
open scoped ComplexOrder

/- English proof (translation)
Establish `hI : (Set.Ioc (-Real.pi) Real.pi).Infinite` using `Set.Ioc_infinite (by linarith [Real.pi_pos])`. Use `Set.infinite_of_injOn_mapsTo (f := fun θ : ℝ => Complex.cos θ + Complex.sin θ * Complex.I) ?_ ?_ hI` and prove the remaining obligations. Introduce `a ha b hb hab`. Establish `h1` using `congrArg Complex.arg hab`. Simplify using `only at h1`.

Rewrite `h1` using `[Complex.arg_cos_add_sin_mul_I ha, Complex.arg_cos_add_sin_mul_I hb]`. Then use the resulting hypothesis. Introduce `θ _`. Conclude with `Complex.norm_cos_add_sin_mul_I θ`.
-/
private theorem setOf_norm_eq_one_infinite : ({z : ℂ | ‖z‖ = 1} : Set ℂ).Infinite := by
  have hI : (Set.Ioc (-Real.pi) Real.pi).Infinite := Set.Ioc_infinite (by linarith [Real.pi_pos])
  refine Set.infinite_of_injOn_mapsTo
    (f := fun θ : ℝ => Complex.cos θ + Complex.sin θ * Complex.I) ?_ ?_ hI
  · intro a ha b hb hab
    have h1 := congrArg Complex.arg hab
    simp only at h1
    rwa [Complex.arg_cos_add_sin_mul_I ha, Complex.arg_cos_add_sin_mul_I hb] at h1
  · intro θ _
    exact Complex.norm_cos_add_sin_mul_I θ

/- English proof (translation)
Rewrite using `[MvPolynomial.funext_set_iff (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => setOf_norm_eq_one_infinite)]`. Introduce `x hx`. Rewrite using `[map_zero]`. Conclude with `h x (fun i => hx i (Set.mem_univ i))`.
-/
theorem cz_torus_zero {ι : Type*} [Fintype ι] (Q : MvPolynomial ι ℂ)
    (h : ∀ z : ι → ℂ, (∀ i, ‖z i‖ = 1) → eval z Q = 0) : Q = 0 := by
  rw [MvPolynomial.funext_set_iff (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => setOf_norm_eq_one_infinite)]
  intro x hx
  rw [map_zero]
  exact h x (fun i => hx i (Set.mem_univ i))

def czFam {N : ℕ} (u v : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin N) ℂ) :
    MvPolynomial (Fin N) ℂ :=
  bind₁ (fun w : Fin N × Fin N => ∑ c : Fin N, C (u w.1 c * v c w.2) * X c) P

/- English proof (translation)
Establish `h1 : eval z (czFam u v P) = eval (fun w : Fin N × Fin N => eval z (∑ c : Fin N, C (u w.1 c * v c w.2) * X c)) P`. Unfold `czFam`. Conclude with `MvPolynomial.eval₂Hom_bind₁ _ _ _ _`. Rewrite using `[h1]`. Unfold `evalM`.

Use `congrArg (fun x => eval x P) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `w`. Simplify using `only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mul_diagonal]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem czFam_eval {N : ℕ} (u v : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin N) ℂ)
    (z : Fin N → ℂ) : eval z (czFam u v P) = evalM (u * diagonal z * v) P := by
  have h1 : eval z (czFam u v P) =
      eval (fun w : Fin N × Fin N => eval z (∑ c : Fin N, C (u w.1 c * v c w.2) * X c)) P := by
    unfold czFam
    exact MvPolynomial.eval₂Hom_bind₁ _ _ _ _
  rw [h1]
  unfold evalM
  refine congrArg (fun x => eval x P) ?_
  funext w
  simp only [map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `h1` using `RCLike.mul_conj (z i)`. Rewrite `h1` using `[hz i]`.

Simplify using `using h1`.
-/
theorem cz_diag_unitary {N : ℕ} (z : Fin N → ℂ) (hz : ∀ i, ‖z i‖ = 1) :
    diagonal z ∈ unitaryGroup (Fin N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have h1 := RCLike.mul_conj (z i)
  rw [hz i] at h1
  simpa using h1

/- English proof (translation)
Establish `hA : (gᴴ * g).IsHermitian` using `Matrix.isHermitian_conjTranspose_mul_self g`. Establish `hnn : ∀ i, 0 ≤ hA.eigenvalues i` using `Matrix.eigenvalues_conjTranspose_mul_self_nonneg g`. Use `set W : Matrix (Fin N) (Fin N) ℂ := (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hW`. Establish `hWu : W ∈ unitaryGroup (Fin N) ℂ` using `hA.eigenvectorUnitary.2`. Establish `hWW : Wᴴ * W = 1`.

Rewrite using `[← Matrix.star_eq_conjTranspose]`. Conclude with `Matrix.mem_unitaryGroup_iff'.mp hWu`. Establish `hWW' : W * Wᴴ = 1`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Conclude with `Matrix.mem_unitaryGroup_iff.mp hWu`.

Establish `hD : Wᴴ * (gᴴ * g) * W = diagonal (RCLike.ofReal ∘ hA.eigenvalues)`. Establish `h1` using `hA.conjStarAlgAut_star_eigenvectorUnitary`. Rewrite `h1` using `[Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star]`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Conclude with `h1`.

Establish `hdet : (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin N) (Fin N) ℂ).det ≠ 0`. Establish `h1 : Wᴴ.det * W.det = 1` using `by rw [← Matrix.det_mul, hWW, Matrix.det_one]`. Establish `h2 : gᴴ.det ≠ 0`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `star_ne_zero.mpr hg.ne_zero`.

Rewrite using `[← hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]`. Conclude with `mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one h1) (mul_ne_zero h2 hg.ne_zero)) (right_ne_zero_of_mul_eq_one h1)`. Establish `hpos : ∀ i, 0 < hA.eigenvalues i`. Introduce `i`. Rewrite `hdet` using `[Matrix.det_diagonal]`.

Establish `h1` using `Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)`. Establish `h2 : hA.eigenvalues i ≠ 0`. Introduce `h3`. Apply `h1` to reduce the goal to its premises. Simplify using `[h3]`.

Conclude with `lt_of_le_of_ne (hnn i) (Ne.symm h2)`. Use `set s : Fin N → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ) with hs`. Establish `hs0 : ∀ i, s i ≠ 0`. Introduce `i`. Simplify using `only [hs, ne_eq, Complex.ofReal_eq_zero]`.

Conclude with `(Real.sqrt_pos.mpr (hpos i)).ne'`. Establish `hs2 : ∀ i, star (s i) * s i = RCLike.ofReal (hA.eigenvalues i)`. Introduce `i`. Express the relevant statement in the definitionally equal form `star (s i) * s i = ((hA.eigenvalues i : ℝ) : ℂ)`. Simplify using `only [hs, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hnn i)]`.

Use `⟨g * W * diagonal (fun i => (s i)⁻¹), ?_, Wᴴ, ?_, s, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]`. Establish `key : diagonal (star fun i => (s i)⁻¹) * (Wᴴ * gᴴ) * (g * W * diagonal fun i => (s i)⁻¹) = diagonal (star fun i => (s i)⁻¹) * (Wᴴ * (gᴴ * g) * W) * diagonal fun i => (s i)⁻¹`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[key, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `h1` using `hs2 i`. Establish `h2 : star (s i) ≠ 0` using `star_ne_zero.mpr (hs0 i)`. Simplify using `only [Pi.star_apply, Function.comp_apply, star_inv₀, ← h1]`.

Clear the denominators using the available nonvanishing facts. Conclude with `div_self (hs0 i)`. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]`. Conclude with `hWW`. Rewrite using `[Matrix.mul_assoc (g * W), Matrix.diagonal_mul_diagonal]`.

Establish `h1 : (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ)`. Use function extensionality and compare the values at `i`. Conclude with `inv_mul_cancel₀ (hs0 i)`. Rewrite using `[h1, Matrix.diagonal_one, Matrix.mul_one, Matrix.mul_assoc, hWW', Matrix.mul_one]`.
-/
theorem cz_svd {N : ℕ} (g : Matrix (Fin N) (Fin N) ℂ) (hg : IsUnit g.det) :
    ∃ u ∈ unitaryGroup (Fin N) ℂ, ∃ v ∈ unitaryGroup (Fin N) ℂ, ∃ z : Fin N → ℂ,
      g = u * diagonal z * v := by
  classical
  have hA : (gᴴ * g).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self g
  have hnn : ∀ i, 0 ≤ hA.eigenvalues i := Matrix.eigenvalues_conjTranspose_mul_self_nonneg g
  set W : Matrix (Fin N) (Fin N) ℂ := (hA.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hW
  have hWu : W ∈ unitaryGroup (Fin N) ℂ := hA.eigenvectorUnitary.2
  have hWW : Wᴴ * W = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff'.mp hWu
  have hWW' : W * Wᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]; exact Matrix.mem_unitaryGroup_iff.mp hWu
  have hD : Wᴴ * (gᴴ * g) * W = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    have h1 := hA.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star] at h1
    rw [← Matrix.star_eq_conjTranspose]
    exact h1
  have hdet : (diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin N) (Fin N) ℂ).det ≠ 0 := by
    have h1 : Wᴴ.det * W.det = 1 := by rw [← Matrix.det_mul, hWW, Matrix.det_one]
    have h2 : gᴴ.det ≠ 0 := by
      rw [Matrix.det_conjTranspose]; exact star_ne_zero.mpr hg.ne_zero
    rw [← hD, Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    exact mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul_eq_one h1)
      (mul_ne_zero h2 hg.ne_zero)) (right_ne_zero_of_mul_eq_one h1)
  have hpos : ∀ i, 0 < hA.eigenvalues i := by
    intro i
    rw [Matrix.det_diagonal] at hdet
    have h1 := Finset.prod_ne_zero_iff.mp hdet i (Finset.mem_univ i)
    have h2 : hA.eigenvalues i ≠ 0 := by
      intro h3
      apply h1
      simp [h3]
    exact lt_of_le_of_ne (hnn i) (Ne.symm h2)
  set s : Fin N → ℂ := fun i => ((Real.sqrt (hA.eigenvalues i) : ℝ) : ℂ) with hs
  have hs0 : ∀ i, s i ≠ 0 := by
    intro i
    simp only [hs, ne_eq, Complex.ofReal_eq_zero]
    exact (Real.sqrt_pos.mpr (hpos i)).ne'
  have hs2 : ∀ i, star (s i) * s i = RCLike.ofReal (hA.eigenvalues i) := by
    intro i
    change star (s i) * s i = ((hA.eigenvalues i : ℝ) : ℂ)
    simp only [hs, Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (hnn i)]
  refine ⟨g * W * diagonal (fun i => (s i)⁻¹), ?_, Wᴴ, ?_, s, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.diagonal_conjTranspose]
    have key : diagonal (star fun i => (s i)⁻¹) * (Wᴴ * gᴴ) * (g * W * diagonal fun i => (s i)⁻¹)
        = diagonal (star fun i => (s i)⁻¹) * (Wᴴ * (gᴴ * g) * W) * diagonal fun i => (s i)⁻¹ := by
      simp only [Matrix.mul_assoc]
    rw [key, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    have h1 := hs2 i
    have h2 : star (s i) ≠ 0 := star_ne_zero.mpr (hs0 i)
    simp only [Pi.star_apply, Function.comp_apply, star_inv₀, ← h1]
    field_simp
    exact div_self (hs0 i)
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact hWW
  · rw [Matrix.mul_assoc (g * W), Matrix.diagonal_mul_diagonal]
    have h1 : (fun i => (s i)⁻¹ * s i) = fun _ => (1 : ℂ) := by
      funext i; exact inv_mul_cancel₀ (hs0 i)
    rw [h1, Matrix.diagonal_one, Matrix.mul_one, Matrix.mul_assoc, hWW', Matrix.mul_one]

/- English proof (translation)
Take `⟨u, hu, v, hv, z, rfl⟩` from `cz_svd g hg`. Establish `hQ : czFam u v P = 0`. Apply `cz_torus_zero` to reduce the goal to its premises. Introduce `w hw`. Rewrite using `[czFam_eval]`.

Conclude with `h _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ hu (cz_diag_unitary w hw)) hv)`. Establish `h1` using `czFam_eval u v P z`. Rewrite `h1` using `[hQ, map_zero]`. Conclude with `h1.symm`.
-/
theorem cz_zariski {N : ℕ} (P : MvPolynomial (Fin N × Fin N) ℂ)
    (h : ∀ u ∈ unitaryGroup (Fin N) ℂ, evalM u P = 0) (g : Matrix (Fin N) (Fin N) ℂ)
    (hg : IsUnit g.det) : evalM g P = 0 := by
  obtain ⟨u, hu, v, hv, z, rfl⟩ := cz_svd g hg
  have hQ : czFam u v P = 0 := by
    apply cz_torus_zero
    intro w hw
    rw [czFam_eval]
    exact h _ (Submonoid.mul_mem _ (Submonoid.mul_mem _ hu (cz_diag_unitary w hw)) hv)
  have h1 := czFam_eval u v P z
  rw [hQ, map_zero] at h1
  exact h1.symm

end PI.WSF
