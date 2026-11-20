import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Model

def sw : Mat 2 1 := (!![0,0,0,0,1; 0,1,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 1,0,0,0,0] : Matrix (Fin 5) (Fin 5) ℂ)

def z0 : Fin (2 * 1 + 2 + 1) → ℂ := (![0,0,0,1,0] : Fin 5 → ℂ)

def z1 : Fin (2 * 1 + 2 + 1) → ℂ := (![0,0,1,2,0] : Fin 5 → ℂ)

def xx : Mat 2 1 := (!![1,-1,0,0,-1/2; 0,1,0,0,1; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1] : Matrix (Fin 5) (Fin 5) ℂ)

def xi : Mat 2 1 := (!![1,1,0,0,-1/2; 0,1,0,0,-1; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1] : Matrix (Fin 5) (Fin 5) ℂ)

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Hpk]`.
-/
theorem hpk_eq : Hpk 2 1 = (!![0,0,0,0,1; 0,1,0,0,0; 0,0,1,0,0; 0,0,0,-1,0; 1,0,0,0,0] : Matrix (Fin 5) (Fin 5) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hpk]

/- English proof (translation)
Simplify using `[herm, Hb, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_succ, Fin.ext_iff]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem herm3 (v w : Fin (2 + 1) → ℂ) : herm (Hb 2) v w =
    star (w (0 : Fin 3)) * v (0 : Fin 3) + star (w (1 : Fin 3)) * v (1 : Fin 3) - star (w (2 : Fin 3)) * v (2 : Fin 3) := by
  simp [herm, Hb, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_succ, Fin.ext_iff]
  ring

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [xx, pEl, herm3, bvec] <;> norm_num`.
-/
theorem xx_eq : xx = pEl 2 1 (fun _ => (![1,0,0] : Fin 3 → ℂ)) 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xx, pEl, herm3, bvec] <;> norm_num

/- English proof (translation)
Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Use `show (xx * xi : Matrix (Fin 5) (Fin 5) ℂ) = 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [xx, xi, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num`.
-/
theorem xx_inv : xx⁻¹ = xi := by
  apply Matrix.inv_eq_right_inv
  show (xx * xi : Matrix (Fin 5) (Fin 5) ℂ) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xx, xi, Matrix.mul_apply, Fin.sum_univ_succ] <;> norm_num

/- English proof (translation)
Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Use `show (sw * sw : Matrix (Fin 5) (Fin 5) ℂ) = 1`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [sw, Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
theorem sw_inv : sw⁻¹ = sw := by
  apply Matrix.inv_eq_right_inv
  show (sw * sw : Matrix (Fin 5) (Fin 5) ℂ) = 1
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sw, Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Use `show swᴴ * Hpk 2 1 * sw = Hpk 2 1`. Rewrite using `[hpk_eq]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [sw, Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
theorem sw_mem : sw ∈ GG 2 1 := by
  show swᴴ * Hpk 2 1 * sw = Hpk 2 1
  rw [hpk_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sw, Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Use `show xxᴴ * Hpk 2 1 * xx = Hpk 2 1`. Rewrite using `[hpk_eq]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [xx, Matrix.mul_apply, Fin.sum_univ_succ, map_ofNat] <;> norm_num`.
-/
theorem xx_mem : xx ∈ GG 2 1 := by
  show xxᴴ * Hpk 2 1 * xx = Hpk 2 1
  rw [hpk_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [xx, Matrix.mul_apply, Fin.sum_univ_succ, map_ofNat] <;> norm_num

/- English proof (translation)
Rewrite using `[hpk_eq]`. Simplify using `[herm, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]`. Put the polynomial expressions in normal form.
-/
theorem herm5 (v w : Fin (2 * 1 + 2 + 1) → ℂ) : herm (Hpk 2 1) v w =
    star (w (0 : Fin 5)) * v (4 : Fin 5) + star (w (1 : Fin 5)) * v (1 : Fin 5) + star (w (2 : Fin 5)) * v (2 : Fin 5)
      - star (w (3 : Fin 5)) * v (3 : Fin 5) + star (w (4 : Fin 5)) * v (0 : Fin 5) := by
  rw [hpk_eq]
  simp [herm, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring_nf

/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> simp [bvec, eI]`.
-/
theorem e0_eq : bvec (eI 2 1 0) = (![1,0,0,0,0] : Fin 5 → ℂ) := by
  ext i; fin_cases i <;> simp [bvec, eI]

/- English proof (translation)
Rewrite using `[← e0_eq]`. Simplify using `[fvec]`.
-/
theorem fvec0 (z) : fvec 2 1 z 0 = (![1,0,0,0,0] : Fin 5 → ℂ) := by
  rw [← e0_eq]; simp [fvec]

/- English proof (translation)
Simplify using `[fvec]`.
-/
theorem fvec1 (z) : fvec 2 1 z 1 = z := by simp [fvec]

/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> simp [sw, dotProduct, Matrix.mulVec, Fin.sum_univ_succ] <;> rfl`.
-/
theorem sw_mulVec (v : Fin (2 * 1 + 2 + 1) → ℂ) : sw *ᵥ v =
    (![v (4 : Fin 5), v (1 : Fin 5), v (2 : Fin 5), v (3 : Fin 5), v (0 : Fin 5)] : Fin 5 → ℂ) := by
  ext i; fin_cases i <;> simp [sw, dotProduct, Matrix.mulVec, Fin.sum_univ_succ] <;> rfl

/- English proof (translation)
Use extensionality with `a b`. Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp [Zhat, fvec0, fvec1, herm5, sw_mulVec, z0, z1]`.
-/
theorem zhat_eq : Zhat 2 1 z0 z1 sw = !![1, 0; 0, -2] := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Zhat, fvec0, fvec1, herm5, sw_mulVec, z0, z1]

/- English proof (translation)
Unfold `Dmin`. Rewrite using `[zhat_eq]`. Simplify using `[Matrix.det_unique]`.
-/
theorem dmin_one : Dmin 2 1 z0 z1 sw ⟨1, by omega⟩ = 1 := by
  unfold Dmin; rw [zhat_eq]; simp [Matrix.det_unique]

/- English proof (translation)
Unfold `Dmin`. Rewrite using `[zhat_eq]`. Use `show (!![1, 0; 0, -2] : Matrix (Fin 2) (Fin 2) ℂ).det = -2`. Simplify using `[Matrix.det_fin_two]`.
-/
theorem dmin_two : Dmin 2 1 z0 z1 sw (Fin.last 2) = -2 := by
  unfold Dmin; rw [zhat_eq]
  show (!![1, 0; 0, -2] : Matrix (Fin 2) (Fin 2) ℂ).det = -2
  simp [Matrix.det_fin_two]

/- English proof (translation)
Unfold `Dr`. Rewrite using `[dmin_one]`. Simplify using the standard rewrite rules.
-/
theorem dr_eq : Dr 2 1 z0 z1 sw = 1 := by unfold Dr; rw [dmin_one]; simp

/- English proof (translation)
Simplify using `[Tz, herm5, z0]`.
-/
theorem tz0 : Tz 2 1 z0 = 1 := by simp [Tz, herm5, z0]
/- English proof (translation)
Simplify using `[Tz, herm5, z1]`. Evaluate the numerical expressions.
-/
theorem tz1 : Tz 2 1 z1 = 3 := by simp [Tz, herm5, z1]; norm_num

/- English proof (translation)
Use `⟨?_, ?_, by rw [tz0]; norm_num, by rw [tz1]; norm_num, sw_mem, ?_, by rw [dr_eq]; norm_num⟩` and prove the remaining obligations. Apply the tactic sequence `intro i hi; fin_cases i <;> simp_all [z0]`. Apply the tactic sequence `intro i hi; fin_cases i <;> simp_all [z1]`. Unfold `Gf`. Rewrite using `[dmin_one, tz0, tz1]`.

Use `dmin_two` as an intermediate fact. Rewrite using `[this]`. Simplify using the standard rewrite rules. Evaluate the numerical expressions.
-/
theorem twoFl : TwoFl 2 1 z0 z1 sw := by
  refine ⟨?_, ?_, by rw [tz0]; norm_num, by rw [tz1]; norm_num, sw_mem, ?_, by rw [dr_eq]; norm_num⟩
  · intro i hi; fin_cases i <;> simp_all [z0]
  · intro i hi; fin_cases i <;> simp_all [z1]
  · unfold Gf; rw [dmin_one, tz0, tz1]
    have := dmin_two
    rw [this]; simp; norm_num

/- English proof (translation)
Apply the tactic sequence `ext i; fin_cases i <;> simp [xx, dotProduct, Matrix.mulVec, Fin.sum_univ_succ] <;> ring`.
-/
theorem xx_mulVec (v : Fin (2 * 1 + 2 + 1) → ℂ) : xx *ᵥ v =
    (![v (0 : Fin 5) - v (1 : Fin 5) - v (4 : Fin 5) / 2, v (1 : Fin 5) + v (4 : Fin 5), v (2 : Fin 5), v (3 : Fin 5),
      v (4 : Fin 5)] : Fin 5 → ℂ) := by
  ext i; fin_cases i <;> simp [xx, dotProduct, Matrix.mulVec, Fin.sum_univ_succ] <;> ring

/- English proof (translation)
Rewrite using `[xx_inv, sw_inv, e0_eq, sw_mulVec]`. Apply the tactic sequence `ext i; fin_cases i <;> simp [xi, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]`.
-/
theorem vec_eq : xx⁻¹ *ᵥ (sw⁻¹ *ᵥ bvec (eI 2 1 0)) = (![-1/2, -1, 0, 0, 1] : Fin 5 → ℂ) := by
  rw [xx_inv, sw_inv, e0_eq, sw_mulVec]
  ext i; fin_cases i <;> simp [xi, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

/- English proof (translation)
Simplify using `only [Ppos, Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hpk_eq]`. Apply the tactic sequence `ext i; fin_cases i <;> simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Matrix.one_apply]`. Rewrite using `[Submodule.mem_sup]`.

Use `⟨(![0, -1, 0, 0, 0] : Fin 5 → ℂ), ?_, bvec (eI 2 1 0), Submodule.subset_span ⟨0, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce `a`. Rewrite using `[sw_inv]`. Apply the tactic sequence `fin_cases a <;> simp [fvec0, fvec1, herm5, sw_mulVec, z0, z1]`. Rewrite using `[xx_mulVec, e0_eq]`.

Apply the tactic sequence `ext i; fin_cases i <;> simp`.
-/
theorem cmHalfIntegralGenerator_mem_algebraicClosure : (WithLp.toLp 2 (![0, -1, 0, 0, 0] : Fin 5 → ℂ) : EuclideanSpace ℂ (Fin (2 * 1 + 2 + 1))) ∈
    Ppos 2 1 z0 z1 sw xx := by
  simp only [Ppos, Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply]
  constructor
  · rw [hpk_eq]
    ext i; fin_cases i <;> simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Matrix.one_apply]
  · rw [Submodule.mem_sup]
    refine ⟨(![0, -1, 0, 0, 0] : Fin 5 → ℂ), ?_, bvec (eI 2 1 0), Submodule.subset_span ⟨0, rfl⟩, ?_⟩
    · intro a
      rw [sw_inv]
      fin_cases a <;> simp [fvec0, fvec1, herm5, sw_mulVec, z0, z1]
    · rw [xx_mulVec, e0_eq]
      ext i; fin_cases i <;> simp

/- English proof (translation)
Simplify using `only [Ppos, Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply] at hp`. Take `⟨h1, h2⟩` from `hp`. Rewrite `h2` using `[Submodule.mem_sup]`. Take `⟨h, hh, y, hy, hs⟩` from `h2`. Establish `h4 : h (4 : Fin 5) = 0`.

Use `(hh 0).1` as an intermediate fact. Simplify `this` using `[fvec0, herm5]`. Establish `y4 : y (4 : Fin 5) = 0`. Unfold `Xsp at hy`. Rewrite `hy` using `[Submodule.mem_span_range_iff_exists_fun]`.

Take `⟨c, rfl⟩` from `hy`. Simplify using `[e0_eq]`. Establish `p4 : p (4 : Fin 5) = 0`. Use `congrFun hs (4 : Fin 5)` as an intermediate fact. Rewrite `this` using `[xx_mulVec]`.

Simplify `this.symm` using `[h4, y4]`. Use `⟨?_, p4⟩` and prove the remaining obligations. Use `congrFun h1 (0 : Fin 5)` as an intermediate fact. Rewrite `this` using `[hpk_eq]`. Simplify using `[dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Matrix.one_apply] at this`.

Establish `p4' : p.ofLp (4 : Fin 5) = 0` using `p4`. Take the linear combination `-this + p4'`.
-/
theorem ppos_coord (p : EuclideanSpace ℂ (Fin (2 * 1 + 2 + 1))) (hp : p ∈ Ppos 2 1 z0 z1 sw xx) :
    p (0 : Fin 5) = 0 ∧ p (4 : Fin 5) = 0 := by
  simp only [Ppos, Submodule.mem_comap, Submodule.mem_inf, LinearMap.mem_ker, Matrix.toLin'_apply] at hp
  obtain ⟨h1, h2⟩ := hp
  rw [Submodule.mem_sup] at h2
  obtain ⟨h, hh, y, hy, hs⟩ := h2
  have h4 : h (4 : Fin 5) = 0 := by
    have := (hh 0).1
    simpa [fvec0, herm5] using this
  have y4 : y (4 : Fin 5) = 0 := by
    unfold Xsp at hy
    rw [Submodule.mem_span_range_iff_exists_fun] at hy
    obtain ⟨c, rfl⟩ := hy
    simp [e0_eq]
  have p4 : p (4 : Fin 5) = 0 := by
    have := congrFun hs (4 : Fin 5)
    rw [xx_mulVec] at this
    simpa [h4, y4] using this.symm
  refine ⟨?_, p4⟩
  have := congrFun h1 (0 : Fin 5)
  rw [hpk_eq] at this
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_succ, Matrix.one_apply] at this
  have p4' : p.ofLp (4 : Fin 5) = 0 := p4
  linear_combination -this + p4'

/- English proof (translation)
Apply `Submodule.eq_starProjection_of_mem_of_inner_eq_zero cmHalfIntegralGenerator_mem_algebraicClosure` to reduce the goal to its premises. Introduce `p hp`. Take `⟨h0, h4⟩` from `ppos_coord p hp`. Simplify using `[PiLp.inner_apply, Fin.sum_univ_succ, h0, h4]`.
-/
theorem proj_eq : (Ppos 2 1 z0 z1 sw xx).starProjection (WithLp.toLp 2 (![-1/2, -1, 0, 0, 1] : Fin 5 → ℂ)) =
    WithLp.toLp 2 (![0, -1, 0, 0, 0] : Fin 5 → ℂ) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero cmHalfIntegralGenerator_mem_algebraicClosure
  intro p hp
  obtain ⟨h0, h4⟩ := ppos_coord p hp
  simp [PiLp.inner_apply, Fin.sum_univ_succ, h0, h4]

/- English proof (translation)
Unfold `Yv gramProj`. Rewrite using `[dr_eq, Matrix.det_unique]`. Simplify using `only [Matrix.gram_apply]`. Rewrite using `[show (default : Fin 1) = 0 from rfl, vec_eq, proj_eq]`. Simplify using `[EuclideanSpace.norm_eq, Fin.sum_univ_succ]`.
-/
theorem yv_eq : Yv 2 1 z0 z1 sw xx = 1 := by
  unfold Yv gramProj
  rw [dr_eq, Matrix.det_unique]
  simp only [Matrix.gram_apply]
  rw [show (default : Fin 1) = 0 from rfl, vec_eq, proj_eq]
  simp [EuclideanSpace.norm_eq, Fin.sum_univ_succ]

/- English proof (translation)
Unfold `Sg`. Rewrite using `[Finset.le_fold_max]`. Conclude with `Or.inl le_rfl`.
-/
theorem one_le_Sg (k r : ℕ) (z) (x : Mat k r) : 1 ≤ Sg k r z x := by
  unfold Sg; rw [Finset.le_fold_max]; exact Or.inl le_rfl

/- English proof (translation)
Use `⟨max (Sg 2 1 z1 xx) (Sg 2 1 z0 (sw * xx)), Matrix.of.symm xx, xx_mem, le_max_left _ _, le_max_right _ _, ?_, ?_⟩` and prove the remaining obligations. Use `show 3 / 4 < Yv 2 1 z0 z1 sw xx`. Rewrite using `[yv_eq]`. Evaluate the numerical expressions. Use `show Yv 2 1 z0 z1 sw xx ≤ _`.

Rewrite using `[yv_eq]`. Evaluate the numerical expressions.
-/
theorem eset_nonempty : ∃ R₀ : ℝ, (Eset 2 1 z0 z1 sw R₀ (3 / 4)).Nonempty := by
  refine ⟨max (Sg 2 1 z1 xx) (Sg 2 1 z0 (sw * xx)), Matrix.of.symm xx, xx_mem, le_max_left _ _, le_max_right _ _, ?_, ?_⟩
  · show 3 / 4 < Yv 2 1 z0 z1 sw xx
    rw [yv_eq]; norm_num
  · show Yv 2 1 z0 z1 sw xx ≤ _
    rw [yv_eq]; norm_num

/- English proof (translation)
Use `⟨le_rfl, fun l hl _ => ?_⟩` and prove the remaining obligations. Use `fin_cases l`. Simplify using `[Dmin]`. Use `dmin_one` as an intermediate fact. Simplify using `at this ⊢`.

Rewrite using `[this]`. Simplify using the standard rewrite rules. Simplify using `at hl`.
-/
theorem deOK : DeOK 2 1 z0 z1 sw 1 := by
  refine ⟨le_rfl, fun l hl _ => ?_⟩
  fin_cases l
  · simp [Dmin]
  · have := dmin_one
    simp at this ⊢
    rw [this]; simp
  · simp at hl

/- English proof (translation)
Establish `hu : upper (r` using `2) (fun _ => a) = !![1, a; 0, 1] := by`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [upper]`. Establish `hi : (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = !![1, -a; 0, 1]`. Apply `Matrix.inv_eq_right_inv` to reduce the goal to its premises. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]`.

Establish `he : uEmb 0 2 !![1, a; 0, 1] = (!![1,a,0,0,0; 0,1,0,0,0; 0,0,1,0,0; 0,0,0,1,-star a; 0,0,0,0,1] : Matrix (Fin 5) (Fin 5) ℂ)`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [uEmb, hi]`. Establish `hH : Hpk 0 2 = (!![0,0,0,0,1; 0,0,0,1,0; 0,0,-1,0,0; 0,1,0,0,0; 1,0,0,0,0] : Matrix (Fin 5) (Fin 5) ℂ)`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Hpk]`. Rewrite using `[hu, he]`.

Use `show _ᴴ * Hpk 0 2 * _ = Hpk 0 2`. Rewrite using `[hH]`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]`.
-/
theorem uEmb_mem (a : ℂ) : uEmb 0 2 (upper fun _ => a) ∈ GG 0 2 := by
  have hu : upper (r := 2) (fun _ => a) = !![1, a; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [upper]
  have hi : (!![1, a; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ = !![1, -a; 0, 1] := by
    apply Matrix.inv_eq_right_inv
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]
  have he : uEmb 0 2 !![1, a; 0, 1] = (!![1,a,0,0,0; 0,1,0,0,0; 0,0,1,0,0; 0,0,0,1,-star a; 0,0,0,0,1] : Matrix (Fin 5) (Fin 5) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [uEmb, hi]
  have hH : Hpk 0 2 = (!![0,0,0,0,1; 0,0,0,1,0; 0,0,-1,0,0; 0,1,0,0,0; 1,0,0,0,0] : Matrix (Fin 5) (Fin 5) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Hpk]
  rw [hu, he]
  show _ᴴ * Hpk 0 2 * _ = Hpk 0 2
  rw [hH]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ]

/- English proof (translation)
Establish `h1 : ∀ v w : Fin (0 + 1) → ℂ, herm (Hb 0) v w = - (star (w 0) * v 0)`. Introduce `v w`. Simplify using `[herm, Hb, dotProduct, Matrix.mulVec_diagonal]`. Establish `he : pOf 0 2 (![fun _ => b₀, fun _ => b₁], fun _ => s, ![t₀, t₁]) = (!![1,0,star b₀, s + star b₀ * b₁ / 2, t₀ * Complex.I + star b₀ * b₀ / 2; 0,1,star b₁, t₁ * Complex.I + star b₁ * b₁ / 2, -star s + star b₁ * b₀ / 2; 0,0,1,b₁,b₀; 0,0,0,1,0; 0,0,0,0,1] : Matrix (Fin 5) (Fin 5) ℂ)`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [pOf, pEl, skewM, h1, bvec] <;> ring`.

Establish `hH : Hpk 0 2 = (!![0,0,0,0,1; 0,0,0,1,0; 0,0,-1,0,0; 0,1,0,0,0; 1,0,0,0,0] : Matrix (Fin 5) (Fin 5) ℂ)`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Hpk]`. Rewrite using `[he]`. Use `show _ᴴ * Hpk 0 2 * _ = Hpk 0 2`. Rewrite using `[hH]`.

Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, map_ofNat] <;> ring`.
-/
theorem pOf_mem (b₀ b₁ s : ℂ) (t₀ t₁ : ℝ) : pOf 0 2 (![fun _ => b₀, fun _ => b₁], fun _ => s, ![t₀, t₁]) ∈ GG 0 2 := by
  have h1 : ∀ v w : Fin (0 + 1) → ℂ, herm (Hb 0) v w = - (star (w 0) * v 0) := by
    intro v w; simp [herm, Hb, dotProduct, Matrix.mulVec_diagonal]
  have he : pOf 0 2 (![fun _ => b₀, fun _ => b₁], fun _ => s, ![t₀, t₁]) =
      (!![1,0,star b₀, s + star b₀ * b₁ / 2, t₀ * Complex.I + star b₀ * b₀ / 2;
          0,1,star b₁, t₁ * Complex.I + star b₁ * b₁ / 2, -star s + star b₁ * b₀ / 2;
          0,0,1,b₁,b₀; 0,0,0,1,0; 0,0,0,0,1] : Matrix (Fin 5) (Fin 5) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [pOf, pEl, skewM, h1, bvec] <;> ring
  have hH : Hpk 0 2 = (!![0,0,0,0,1; 0,0,0,1,0; 0,0,-1,0,0; 0,1,0,0,0; 1,0,0,0,0] : Matrix (Fin 5) (Fin 5) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Hpk]
  rw [he]
  show _ᴴ * Hpk 0 2 * _ = Hpk 0 2
  rw [hH]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, map_ofNat] <;> ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
example {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) :
    (volume : Measure (lieE S)) = (stdOrthonormalBasis ℝ (lieE S)).toBasis.addHaar := rfl

/- English proof (translation)
Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Unfold `upper`. Apply the tactic sequence `split_ifs <;> fun_prop`.
-/
theorem cont_upper (r : ℕ) : Continuous (upper : (UT r → ℂ) → Matrix (Fin r) (Fin r) ℂ) := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  unfold upper
  split_ifs <;> fun_prop

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
/- English proof (translation)
Rewrite using `[Matrix.det_of_upperTriangular]`. Conclude with `Finset.prod_eq_one fun i _ => by simp [_root_.GlobalTheory.Amp.upper]`. Introduce `i j hij`. Simplify using `only [id] at hij`. Establish `h1 : ¬ i < j` using `not_lt.mpr hij.le`.

Simplify using `[_root_.GlobalTheory.Amp.upper, h1, hij.ne']`.
-/
theorem _root_.GlobalTheory.Amp.Model.det_upper {r : ℕ} (x : _root_.GlobalTheory.Amp.UT r → ℂ) :
    (_root_.GlobalTheory.Amp.upper x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [_root_.GlobalTheory.Amp.upper]
  · intro i j hij
    simp only [id] at hij
    have h1 : ¬ i < j := not_lt.mpr hij.le
    simp [_root_.GlobalTheory.Amp.upper, h1, hij.ne']

/- English proof (translation)
Establish `: (fun x : UT r → ℂ => (upper x)⁻¹) = fun x => (upper x).adjugate`. Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.inv_def, det_upper]`. Simplify using the standard rewrite rules. Rewrite using `[this]`.

Conclude with `(cont_upper r).matrix_adjugate`.
-/
theorem cont_upper_inv (r : ℕ) : Continuous fun x : UT r → ℂ => (upper x)⁻¹ := by
  have : (fun x : UT r → ℂ => (upper x)⁻¹) = fun x => (upper x).adjugate := by
    funext x; rw [Matrix.inv_def, det_upper]; simp
  rw [this]; exact (cont_upper r).matrix_adjugate

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
/- English proof (translation)
Establish `hup : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ => _root_.GlobalTheory.Amp.upper x`. Use `continuous_pi fun a => continuous_pi fun b => ?_` and prove the remaining obligations. Unfold `_root_.GlobalTheory.Amp.upper`. Use `split_ifs`. Conclude with `continuous_apply _`.

Conclude with `continuous_const`. Conclude with `continuous_const`. Establish `hinv : ∀ x : _root_.GlobalTheory.Amp.UT r → ℂ, (_root_.GlobalTheory.Amp.upper x)⁻¹ = (_root_.GlobalTheory.Amp.upper x).adjugate`. Introduce `x`. Rewrite using `[Matrix.inv_def, _root_.GlobalTheory.Amp.Model.det_upper]`.

Simplify using the standard rewrite rules. Establish `hc : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ => (_root_.GlobalTheory.Amp.upper x)⁻¹`. Repeatedly rewrite using `[hinv]`. Conclude with `hup.matrix_adjugate`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations.

Unfold `_root_.GlobalTheory.Amp.uEmb`. Use `split_ifs`. Conclude with `(continuous_apply_apply _ _).comp hup`. Conclude with `((continuous_apply_apply _ _).comp hc).star`. Conclude with `continuous_const`.

Conclude with `continuous_const`.
-/
theorem _root_.GlobalTheory.Amp.Model.cont_uEmb (k r : ℕ) :
    Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      _root_.GlobalTheory.Amp.uEmb k r (_root_.GlobalTheory.Amp.upper x) := by
  have hup : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      _root_.GlobalTheory.Amp.upper x := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold _root_.GlobalTheory.Amp.upper
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
    · exact continuous_const
  have hinv : ∀ x : _root_.GlobalTheory.Amp.UT r → ℂ,
      (_root_.GlobalTheory.Amp.upper x)⁻¹ = (_root_.GlobalTheory.Amp.upper x).adjugate := by
    intro x; rw [Matrix.inv_def, _root_.GlobalTheory.Amp.Model.det_upper]; simp
  have hc : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      (_root_.GlobalTheory.Amp.upper x)⁻¹ := by
    simp_rw [hinv]; exact hup.matrix_adjugate
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold _root_.GlobalTheory.Amp.uEmb
  split_ifs
  · exact (continuous_apply_apply _ _).comp hup
  · exact ((continuous_apply_apply _ _).comp hc).star
  · exact continuous_const
  · exact continuous_const

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
/- English proof (translation)
Establish `herm : ∀ {f g : _root_.GlobalTheory.Amp.PPar k r → Fin (k + 1) → ℂ}, Continuous f → Continuous g → Continuous fun q => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hb k) (f q) (g q)` using `fun hf hg => (_root_.Formalism.FourierDecayAlt.P.B2x5.continuous_herm (_root_.Formalism.QuantumDeterminants.Hb k)).comp (hf.prodMk hg)`. Establish `hB : ∀ a, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r => q.1 a` using `fun a => (continuous_apply a).comp continuous_fst`. Establish `hS : ∀ a b, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r => _root_.GlobalTheory.Amp.skewM q.2.1 q.2.2 a b`. Introduce `a b`. Unfold `_root_.GlobalTheory.Amp.skewM`.

Use `split_ifs`. Conclude with `(continuous_apply _).comp (continuous_fst.comp continuous_snd)`. Conclude with `((continuous_apply _).comp (continuous_fst.comp continuous_snd)).star.neg`. Conclude with `(Complex.continuous_ofReal.comp ((continuous_apply _).comp (continuous_snd.comp continuous_snd))).mul continuous_const`. Use `continuous_pi fun i => continuous_pi fun j => ?_` and prove the remaining obligations.

Unfold `_root_.GlobalTheory.Amp.pOf _root_.GlobalTheory.Amp.pEl`. Use `split_ifs`. Conclude with `continuous_const`. Conclude with `(herm continuous_const (hB _)).neg`. Conclude with `(continuous_apply _).comp (hB _)`.

Conclude with `(hS _ _).sub ((herm (hB _) (hB _)).div_const _)`. Conclude with `continuous_const`.
-/
theorem _root_.GlobalTheory.Amp.Model.cont_pOf (k r : ℕ) :
    Continuous (_root_.GlobalTheory.Amp.pOf k r) := by
  have herm : ∀ {f g : _root_.GlobalTheory.Amp.PPar k r → Fin (k + 1) → ℂ},
      Continuous f → Continuous g → Continuous fun q => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hb k) (f q) (g q) :=
    fun hf hg => (_root_.Formalism.FourierDecayAlt.P.B2x5.continuous_herm (_root_.Formalism.QuantumDeterminants.Hb k)).comp (hf.prodMk hg)
  have hB : ∀ a, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r => q.1 a :=
    fun a => (continuous_apply a).comp continuous_fst
  have hS : ∀ a b, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r =>
      _root_.GlobalTheory.Amp.skewM q.2.1 q.2.2 a b := by
    intro a b
    unfold _root_.GlobalTheory.Amp.skewM
    split_ifs
    · exact (continuous_apply _).comp (continuous_fst.comp continuous_snd)
    · exact ((continuous_apply _).comp (continuous_fst.comp continuous_snd)).star.neg
    · exact (Complex.continuous_ofReal.comp
        ((continuous_apply _).comp (continuous_snd.comp continuous_snd))).mul continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold _root_.GlobalTheory.Amp.pOf _root_.GlobalTheory.Amp.pEl
  split_ifs
  · exact continuous_const
  · exact (herm continuous_const (hB _)).neg
  · exact (continuous_apply _).comp (hB _)
  · exact (hS _ _).sub ((herm (hB _) (hB _)).div_const _)
  · exact continuous_const

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
/- English proof (translation)
Conclude with `((_root_.GlobalTheory.Amp.Model.cont_uEmb k r).comp continuous_fst).matrix_mul ((_root_.GlobalTheory.Amp.Model.cont_pOf k r).comp continuous_snd)`.
-/
theorem _root_.GlobalTheory.Amp.Model.cont_lebN_map (k r : ℕ) :
    Continuous fun q : (_root_.GlobalTheory.Amp.UT r → ℂ) × _root_.GlobalTheory.Amp.PPar k r =>
      (Matrix.of.symm (_root_.GlobalTheory.Amp.uEmb k r (_root_.GlobalTheory.Amp.upper q.1) *
        _root_.GlobalTheory.Amp.pOf k r q.2) : _root_.Formalism.QuantumDeterminants.Mt k r) := by
  exact ((_root_.GlobalTheory.Amp.Model.cont_uEmb k r).comp continuous_fst).matrix_mul
    ((_root_.GlobalTheory.Amp.Model.cont_pOf k r).comp continuous_snd)

/- English proof (translation)
Introduce `h`. Use `congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h` as an intermediate fact. Simplify using `only [lebN] at this`. Rewrite `this` using `[Measure.map_apply (cont_lebN_map k r).measurable MeasurableSet.univ]`. Use `haveI h1 : (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure`.

Use `haveI h0 : (volume : Measure (Fin (k + 1) → ℂ)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _`. Use `haveI h0' : (volume : Measure (Fin r → Fin (k + 1) → ℂ)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _`. Use `haveI s1 : SFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := Measure.prod.instSFinite`. Use `haveI s2 : SFinite (volume : Measure (PPar k r)) := Measure.prod.instSFinite`. Use `haveI h2 : (volume : Measure (PPar k r)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure`.

Use `haveI h3 : (volume : Measure ((UT r → ℂ) × PPar k r)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure`. Conclude with `(isOpen_univ.measure_pos (volume : Measure ((UT r → ℂ) × PPar k r)) Set.univ_nonempty).ne' (by simpa using this)`.
-/
theorem lebN_ne_zero (k r : ℕ) : lebN k r ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure (Mt k r) => μ Set.univ) h
  simp only [lebN] at this
  rw [Measure.map_apply (cont_lebN_map k r).measurable MeasurableSet.univ] at this
  haveI h1 : (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  haveI h0 : (volume : Measure (Fin (k + 1) → ℂ)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  haveI h0' : (volume : Measure (Fin r → Fin (k + 1) → ℂ)).IsOpenPosMeasure := Measure.pi.isOpenPosMeasure _
  haveI s1 : SFinite (volume : Measure ((UT r → ℂ) × (Fin r → ℝ))) := Measure.prod.instSFinite
  haveI s2 : SFinite (volume : Measure (PPar k r)) := Measure.prod.instSFinite
  haveI h2 : (volume : Measure (PPar k r)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  haveI h3 : (volume : Measure ((UT r → ℂ) × PPar k r)).IsOpenPosMeasure := Measure.prod.instIsOpenPosMeasure
  exact (isOpen_univ.measure_pos (volume : Measure ((UT r → ℂ) × PPar k r)) Set.univ_nonempty).ne' (by simpa using this)

/- English proof (translation)
Assemble the required witnesses or components as `⟨Metric.measure_ball_pos _ _ h, measure_ball_lt_top⟩`.
-/
theorem ball_pos_fin {m : ℕ} (S : Set (Matrix (Fin m) (Fin m) ℂ)) {ρ : ℝ} (h : 0 < ρ) :
    0 < volume (Metric.ball (0 : lieE S) ρ) ∧ volume (Metric.ball (0 : lieE S) ρ) < ⊤ :=
  ⟨Metric.measure_ball_pos _ _ h, measure_ball_lt_top⟩

/- English proof (translation)
The claim follows from `tendsto_nhds_unique h h'`.
-/
theorem hasDens_unique {m : ℕ} {S : Set (Matrix (Fin m) (Fin m) ℂ)} {μ} {c c' : ℝ≥0∞}
    (h : HasDens S μ c) (h' : HasDens S μ c') : c = c' := tendsto_nhds_unique h h'

end GlobalTheory.Amp.Model
