import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GaussianPlaneIntegrals.AssemblyAlt

noncomputable section

open MvPolynomial Matrix Complex Filter Topology
open scoped ComplexConjugate ComplexOrder

namespace PositivityTheory.Rg.Sw.FFTSteps

variable {ι A B : Type} [Fintype ι] [DecidableEq ι]

/- English proof (translation)
Establish `hinj : Function.Injective g.mulVec` using `Matrix.mulVec_injective_iff_isUnit.mpr hg`. Establish `hM : (gᴴ * g).PosDef` using `Matrix.PosDef.conjTranspose_mul_self g hinj`. Establish `hspec : gᴴ * g = (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) * diagonal (fun i => (hM.1.eigenvalues i : ℂ)) * star (hM.1.eigenvectorUnitary : Matrix ι ι ℂ)`. Establish `h` using `hM.1.spectral_theorem`. Rewrite `h` using `[Unitary.conjStarAlgAut_apply]`.

Conclude with `h`. Establish `hVmem : (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ` using `hM.1.eigenvectorUnitary.2`. Generalize the expression as in `(hM.1.eigenvectorUnitary : Matrix ι ι ℂ) = V at hspec hVmem`. Establish `hV1 : star V * V = 1` using `Matrix.mem_unitaryGroup_iff'.mp hVmem`. Establish `hV2 : V * star V = 1` using `Matrix.mem_unitaryGroup_iff.mp hVmem`.

Establish `hlpos : ∀ i, 0 < hM.1.eigenvalues i` using `fun i => hM.eigenvalues_pos i`. Generalize the expression as in `hM.1.eigenvalues = l at hspec hlpos`. Use `set a : ι → ℝ := fun i => Real.log (l i) / 2 with ha`. Establish `hDD : diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * diagonal (fun i => cexp (a i)) = 1`. Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Complex.ofReal_exp, ← Complex.exp_add]`. Simplify using the standard rewrite rules. Establish `hDs : star (diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ))) = diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ))`.

Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `Complex.conj_ofReal _`. Establish `hreal : ∀ i, Real.exp (-(a i)) * l i * Real.exp (-(a i)) = 1`.

Introduce `i`. Establish `h2 : Real.exp (-(a i)) * Real.exp (-(a i)) = (l i)⁻¹`. Rewrite using `[← Real.exp_add, show -(a i) + -(a i) = -Real.log (l i) by simp only [ha]; ring, Real.exp_neg, Real.exp_log (hlpos i)]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)), star V, a, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.mem_unitaryGroup_iff']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[star_mul, star_mul, hDs, Matrix.star_eq_conjTranspose g]`. Simplify using `only [mul_assoc]`. Use `_ = diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * diagonal (fun i => (l i : ℂ)) * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by`.

Rewrite using `[hspec, show star V * (V * diagonal (fun i => (l i : ℂ)) * star V) * V = diagonal (fun i => (l i : ℂ)) by`. Simplify using `only [← mul_assoc, hV1, one_mul]`. Rewrite using `[mul_assoc, hV1, mul_one]]`. Use `_ = 1 := by`. Rewrite using `[diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hreal i` after adjusting the coercions. Conclude with `Unitary.star_mem hVmem`. Rewrite using `[mul_assoc (g * V), hDD, mul_one, mul_assoc, hV2, mul_one]`.
-/
theorem exists_unitary_diagonal_unitary' (g : Matrix ι ι ℂ) (hg : IsUnit g) :
    ∃ (u₁ u₂ : Matrix ι ι ℂ) (a : ι → ℝ), u₁ ∈ Matrix.unitaryGroup ι ℂ ∧
      u₂ ∈ Matrix.unitaryGroup ι ℂ ∧ g = u₁ * diagonal (fun i => cexp (a i)) * u₂ := by
  classical
  have hinj : Function.Injective g.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hg
  have hM : (gᴴ * g).PosDef := Matrix.PosDef.conjTranspose_mul_self g hinj
  have hspec : gᴴ * g = (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) *
      diagonal (fun i => (hM.1.eigenvalues i : ℂ)) * star (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) := by
    have h := hM.1.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    exact h
  have hVmem : (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) ∈ Matrix.unitaryGroup ι ℂ :=
    hM.1.eigenvectorUnitary.2
  generalize (hM.1.eigenvectorUnitary : Matrix ι ι ℂ) = V at hspec hVmem
  have hV1 : star V * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hVmem
  have hV2 : V * star V = 1 := Matrix.mem_unitaryGroup_iff.mp hVmem
  have hlpos : ∀ i, 0 < hM.1.eigenvalues i := fun i => hM.eigenvalues_pos i
  generalize hM.1.eigenvalues = l at hspec hlpos
  set a : ι → ℝ := fun i => Real.log (l i) / 2 with ha
  have hDD : diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * diagonal (fun i => cexp (a i)) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    simp
  have hDs : star (diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ))) =
      diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    exact Complex.conj_ofReal _
  have hreal : ∀ i, Real.exp (-(a i)) * l i * Real.exp (-(a i)) = 1 := by
    intro i
    have h2 : Real.exp (-(a i)) * Real.exp (-(a i)) = (l i)⁻¹ := by
      rw [← Real.exp_add, show -(a i) + -(a i) = -Real.log (l i) by simp only [ha]; ring,
        Real.exp_neg, Real.exp_log (hlpos i)]
    calc Real.exp (-(a i)) * l i * Real.exp (-(a i))
        = (Real.exp (-(a i)) * Real.exp (-(a i))) * l i := by ring
      _ = 1 := by rw [h2, inv_mul_cancel₀ (hlpos i).ne']
  refine ⟨g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)), star V, a, ?_, ?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff']
    calc star (g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ))) *
          (g * V * diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)))
        = diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * (star V * (gᴴ * g) * V) *
            diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by
          rw [star_mul, star_mul, hDs, Matrix.star_eq_conjTranspose g]
          simp only [mul_assoc]
      _ = diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) * diagonal (fun i => (l i : ℂ)) *
            diagonal (fun i => ((Real.exp (-(a i)) : ℝ) : ℂ)) := by
          rw [hspec, show star V * (V * diagonal (fun i => (l i : ℂ)) * star V) * V
              = diagonal (fun i => (l i : ℂ)) by
            simp only [← mul_assoc, hV1, one_mul]
            rw [mul_assoc, hV1, mul_one]]
      _ = 1 := by
          rw [diagonal_mul_diagonal, diagonal_mul_diagonal, ← diagonal_one]
          congr 1
          funext i
          exact_mod_cast hreal i
  · exact Unitary.star_mem hVmem
  · rw [mul_assoc (g * V), hDD, mul_one, mul_assoc, hV2, mul_one]

def actZ (g h : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) : (ι × A) ⊕ (ι × B) → ℂ :=
  Sum.elim (fun x => ∑ j, g x.1 j * z (Sum.inl (j, x.2))) (fun y => ∑ j, h y.1 j * z (Sum.inr (j, y.2)))

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [sub]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp]`.

Use `congr 1`. Break down `v with x | y` into its components or cases. Simplify using `[sub, actZ]`. Simplify using `[sub, actZ]`.
-/
theorem eval_sub (g h : Matrix ι ι ℂ) (p : PV ι A B) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval z (sub g h p) = eval (actZ g h z) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [sub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp]
    congr 1
    rcases v with x | y
    · simp [sub, actZ]
    · simp [sub, actZ]

omit [DecidableEq ι] in
/- English proof (translation)
Use function extensionality and compare the values at `v`. Break down `v with x | y` into its components or cases. Simplify using `only [actZ, Sum.elim_inl, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`. Conclude with `Finset.sum_comm`. Simplify using `only [actZ, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]`.

Conclude with `Finset.sum_comm`.
-/
theorem actZ_mul (g h g' h' : Matrix ι ι ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actZ (g * g') (h * h') z = actZ g h (actZ g' h' z) := by
  funext v
  rcases v with x | y
  · simp only [actZ, Sum.elim_inl, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  · simp only [actZ, Sum.elim_inr, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm

/- English proof (translation)
Use function extensionality and compare the values at `v`. Break down `v with x | y` into its components or cases. Simplify using `[actZ, diagonal_apply]`. Simplify using `[actZ, diagonal_apply]`.
-/
theorem actZ_diagonal (a b : ι → ℂ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    actZ (diagonal a) (diagonal b) z = Sum.elim (fun x => a x.1 * z (Sum.inl x)) (fun y => b y.1 * z (Sum.inr y)) := by
  funext v
  rcases v with x | y
  · simp [actZ, diagonal_apply]
  · simp [actZ, diagonal_apply]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp`. Consider the case `add p q hp hq`. Simplify using `only [map_add]`. Conclude with `hp.add hq`.

Consider the case `mul_X p v hp`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Conclude with `hp.mul (hf v)`.
-/
theorem differentiable_eval' {σ : Type} (p : MvPolynomial σ ℂ) (f : ℂ → σ → ℂ)
    (hf : ∀ v, Differentiable ℂ (fun c => f c v)) :
    Differentiable ℂ (fun c => MvPolynomial.eval (f c) p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p v hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (hf v)

/- English proof (translation)
Rewrite using `[← eval_sub, hp u hu]`.
-/
theorem eval_inv (p : PV ι A B) (hp : IsInv p) (u : Matrix ι ι ℂ) (hu : u ∈ Matrix.unitaryGroup ι ℂ)
    (z : (ι × A) ⊕ (ι × B) → ℂ) : eval (actZ u (u.map star) z) p = eval z p := by
  rw [← eval_sub, hp u hu]

/- English proof (translation)
Use `set F : ℂ → ℂ := fun c => eval (actZ (diagonal fun i => cexp (c * a i)) (diagonal fun i => cexp (-(c * a i))) z) p with hF`. Establish `hdiff : Differentiable ℂ F`. Establish `hF' : F = fun c => eval (Sum.elim (fun x : ι × A => cexp (c * a x.1) * z (Sum.inl x)) (fun y : ι × B => cexp (-(c * a y.1)) * z (Sum.inr y))) p`. Use function extensionality and compare the values at `c`. Simplify using `only [hF, actZ_diagonal]`.

Rewrite using `[hF']`. Apply `differentiable_eval'` to reduce the goal to its premises. Introduce `v`. Break down `v with x | y` into its components or cases. Simplify using `only [Sum.elim_inl] fun_prop`.

Simplify using `only [Sum.elim_inr] fun_prop`. Establish `himag : ∀ t : ℝ, F (I * t) = eval z p`. Introduce `t`. Establish `hs : ∀ i, star (cexp (I * t * a i)) = cexp (-(I * t * a i))`. Introduce `i`.

Rewrite using `[show star (cexp (I * t * a i)) = conj (cexp (I * t * a i)) from rfl, ← Complex.exp_conj]`. Use `congr 1`. Simplify using `only [map_mul, Complex.conj_I, Complex.conj_ofReal]`. Expand and normalize the polynomial expressions, which then agree. Establish `hu : (diagonal fun i => cexp (I * t * a i)) ∈ Matrix.unitaryGroup ι ℂ`.

Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Pi.star_apply, hs i, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]`. Establish `hmap : (diagonal fun i => cexp (I * t * a i)).map star = diagonal fun i => cexp (-(I * t * a i))`.

Rewrite using `[Matrix.diagonal_map (star_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hs i`. Use `show eval (actZ (diagonal fun i => cexp (I * t * a i)) (diagonal fun i => cexp (-(I * t * a i))) z) p = eval z p`.

Rewrite using `[← hmap]`. Conclude with `eval_inv p hp _ hu z`. Establish `hconst : F 1 = eval z p`. Establish `han : AnalyticOnNhd ℂ F Set.univ` using `analyticOnNhd_univ_iff_differentiable.mpr hdiff`. Establish `hg : AnalyticOnNhd ℂ (fun _ : ℂ => eval z p) Set.univ` using `analyticOnNhd_const`.

Establish `hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), F w = eval z p`. Establish `ht : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0)`. Apply `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within` to reduce the goal to its premises. Establish `hc : Continuous (fun t : ℝ => I * (t : ℂ))` using `by fun_prop`. Establish `h0 : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝 0) (𝓝 0)` using `by simpa using hc.tendsto 0`.

Conclude with `h0.mono_left nhdsWithin_le_nhds`. Use `filter_upwards [self_mem_nhdsWithin] with t ht`. Simplify `ht` using `[Complex.I_ne_zero]`. Conclude with `ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun t => himag t))`. Conclude with `han.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (Set.mem_univ 0) hfreq (Set.mem_univ 1)`.

Simplify `hconst` using `[hF]`.
-/
theorem eval_diag (p : PV ι A B) (hp : IsInv p) (a : ι → ℝ) (z : (ι × A) ⊕ (ι × B) → ℂ) :
    eval (actZ (diagonal fun i => cexp (a i)) (diagonal fun i => cexp (-(a i : ℂ))) z) p = eval z p := by
  set F : ℂ → ℂ := fun c => eval (actZ (diagonal fun i => cexp (c * a i))
    (diagonal fun i => cexp (-(c * a i))) z) p with hF
  have hdiff : Differentiable ℂ F := by
    have hF' : F = fun c => eval (Sum.elim (fun x : ι × A => cexp (c * a x.1) * z (Sum.inl x))
        (fun y : ι × B => cexp (-(c * a y.1)) * z (Sum.inr y))) p := by
      funext c
      simp only [hF, actZ_diagonal]
    rw [hF']
    apply differentiable_eval'
    intro v
    rcases v with x | y
    · simp only [Sum.elim_inl]
      fun_prop
    · simp only [Sum.elim_inr]
      fun_prop
  have himag : ∀ t : ℝ, F (I * t) = eval z p := by
    intro t
    have hs : ∀ i, star (cexp (I * t * a i)) = cexp (-(I * t * a i)) := by
      intro i
      rw [show star (cexp (I * t * a i)) = conj (cexp (I * t * a i)) from rfl, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    have hu : (diagonal fun i => cexp (I * t * a i)) ∈ Matrix.unitaryGroup ι ℂ := by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [Pi.star_apply, hs i, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
    have hmap : (diagonal fun i => cexp (I * t * a i)).map star =
        diagonal fun i => cexp (-(I * t * a i)) := by
      rw [Matrix.diagonal_map (star_zero _)]
      congr 1
      funext i
      exact hs i
    show eval (actZ (diagonal fun i => cexp (I * t * a i)) (diagonal fun i => cexp (-(I * t * a i))) z) p
      = eval z p
    rw [← hmap]
    exact eval_inv p hp _ hu z
  have hconst : F 1 = eval z p := by
    have han : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_univ_iff_differentiable.mpr hdiff
    have hg : AnalyticOnNhd ℂ (fun _ : ℂ => eval z p) Set.univ := analyticOnNhd_const
    have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), F w = eval z p := by
      have ht : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
        apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · have hc : Continuous (fun t : ℝ => I * (t : ℂ)) := by fun_prop
          have h0 : Tendsto (fun t : ℝ => I * (t : ℂ)) (𝓝 0) (𝓝 0) := by simpa using hc.tendsto 0
          exact h0.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simpa [Complex.I_ne_zero] using ht
      exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall fun t => himag t))
    exact han.eqOn_of_preconnected_of_frequently_eq hg isPreconnected_univ (Set.mem_univ 0) hfreq
      (Set.mem_univ 1)
  simpa [hF] using hconst

/- English proof (translation)
Introduce `ι A B _ _ _ _ p hp g h hgh`. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `z`. Establish `hg : IsUnit g` using `(Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_right_inverse hgh)`. Take `⟨u₁, u₂, a, hu₁, hu₂, hfac⟩` from `exists_unitary_diagonal_unitary' g hg`.

Establish `hcancel : ∀ {P Q : Matrix ι ι ℂ} (X : Matrix ι ι ℂ), P * Q = 1 → P * (Q * X) = X`. Introduce `P Q X hPQ`. Rewrite using `[← mul_assoc, hPQ, one_mul]`. Establish `hu1s : u₁ * u₁ᴴ = 1`. Rewrite using `[← Matrix.star_eq_conjTranspose]`.

Conclude with `Matrix.mem_unitaryGroup_iff.mp hu₁`. Establish `hu2s : u₂ * u₂ᴴ = 1`. Rewrite using `[← Matrix.star_eq_conjTranspose]`. Conclude with `Matrix.mem_unitaryGroup_iff.mp hu₂`. Establish `hDD : diagonal (fun i => cexp (a i)) * diagonal (fun i => cexp (-(a i : ℂ))) = 1`.

Rewrite using `[diagonal_mul_diagonal, ← diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[← Complex.exp_add, add_neg_cancel, Complex.exp_zero]`. Establish `hK : g * (u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ) = 1`.

Rewrite using `[hfac]`. Simplify using `only [mul_assoc]`. Rewrite using `[hcancel _ hu2s, hcancel _ hDD, hu1s]`. Establish `hT : hᵀ = u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ`. Establish `h1 : hᵀ * g = 1` using `_root_.mul_eq_one_comm.mp hgh`.

Combine the equalities or inequalities in the displayed calculation. Establish `hct : ∀ M : Matrix ι ι ℂ, Mᴴᵀ = M.map star`. Introduce `M`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Establish `hh : h = u₁.map star * diagonal (fun i => cexp (-(a i : ℂ))) * u₂.map star`. Rewrite using `[← Matrix.transpose_transpose h, hT, Matrix.transpose_mul, Matrix.transpose_mul, hct, hct, Matrix.diagonal_transpose, mul_assoc]`. Rewrite using `[eval_sub, hfac, hh, actZ_mul, actZ_mul, eval_inv p hp u₁ hu₁, eval_diag p hp a, eval_inv p hp u₂ hu₂]`.
-/
theorem ext : Ext := by
  intro ι A B _ _ _ _ p hp g h hgh
  apply MvPolynomial.funext
  intro z
  have hg : IsUnit g := (Matrix.isUnit_iff_isUnit_det g).mpr (Matrix.isUnit_det_of_right_inverse hgh)
  obtain ⟨u₁, u₂, a, hu₁, hu₂, hfac⟩ := exists_unitary_diagonal_unitary' g hg
  have hcancel : ∀ {P Q : Matrix ι ι ℂ} (X : Matrix ι ι ℂ), P * Q = 1 → P * (Q * X) = X := by
    intro P Q X hPQ
    rw [← mul_assoc, hPQ, one_mul]
  have hu1s : u₁ * u₁ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hu₁
  have hu2s : u₂ * u₂ᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hu₂
  have hDD : diagonal (fun i => cexp (a i)) * diagonal (fun i => cexp (-(a i : ℂ))) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  have hK : g * (u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ) = 1 := by
    rw [hfac]
    simp only [mul_assoc]
    rw [hcancel _ hu2s, hcancel _ hDD, hu1s]
  have hT : hᵀ = u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ := by
    have h1 : hᵀ * g = 1 := _root_.mul_eq_one_comm.mp hgh
    calc hᵀ = hᵀ * (g * (u₂ᴴ * diagonal (fun i => cexp (-(a i : ℂ))) * u₁ᴴ)) := by rw [hK, mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have hct : ∀ M : Matrix ι ι ℂ, Mᴴᵀ = M.map star := by
    intro M
    ext i j
    simp
  have hh : h = u₁.map star * diagonal (fun i => cexp (-(a i : ℂ))) * u₂.map star := by
    rw [← Matrix.transpose_transpose h, hT, Matrix.transpose_mul, Matrix.transpose_mul, hct, hct,
      Matrix.diagonal_transpose, mul_assoc]
  rw [eval_sub, hfac, hh, actZ_mul, actZ_mul, eval_inv p hp u₁ hu₁, eval_diag p hp a,
    eval_inv p hp u₂ hu₂]

end PositivityTheory.Rg.Sw.FFTSteps
