import ReciprocityTheory.L2DbarEstimates.LeviForms.BergmanExistsStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply

universe u

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff

noncomputable section

/- English proof (translation)
The claim follows from `((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2.clm_apply contDiffOn_const`.
-/
theorem macof_fderiv_apply_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (u : V n) : ContDiffOn ℝ ∞ (fun y => fderiv ℝ g y u) U := ((contDiffOn_infty_iff_fderiv_of_isOpen hU).1 hg).2.clm_apply contDiffOn_const

/- English proof (translation)
Unfold `wd`. Conclude with `((macof_fderiv_apply_contDiffOn hU hg _).sub (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2`.
-/
theorem macof_wd_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) : ContDiffOn ℝ ∞ (wd n j g) U := by
  unfold wd
  exact ((macof_fderiv_apply_contDiffOn hU hg _).sub
    (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2

/- English proof (translation)
Unfold `wdb`. Conclude with `((macof_fderiv_apply_contDiffOn hU hg _).add (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2`.
-/
theorem macof_wdb_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : V n → ℂ}
    (hg : ContDiffOn ℝ ∞ g U) (j : Fin n) : ContDiffOn ℝ ∞ (wdb n j g) U := by
  unfold wdb
  exact ((macof_fderiv_apply_contDiffOn hU hg _).add
    (contDiffOn_const.mul (macof_fderiv_apply_contDiffOn hU hg _))).div_const 2

def macofDet (n : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin n → ℂ) ℂ where
  toMultilinearMap :=
    ((Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap).restrictScalars ℝ
  cont := by
    show Continuous fun v : Fin n → Fin n → ℂ => Matrix.det (Matrix.of v)
    exact continuous_id.matrix_det

def macofRow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : (Fin n → ℂ) →ₗ[ℂ] ℂ :=
  (Matrix.detRowAlternating : (Fin n → ℂ) [⋀^Fin n]→ₗ[ℂ] ℂ).toMultilinearMap.toLinearMap M i

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem macofRow_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) (u : Fin n → ℂ) :
    macofRow M i u = (M.updateRow i u).det := rfl

/- English proof (translation)
Establish `hrows : HasFDerivAt (fun w => (fun i l => B w i l : Fin n → Fin n → ℂ)) (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l) y` using `hasFDerivAt_pi.2 fun i => hasFDerivAt_pi.2 fun l => hB i l`. Establish `hcomp` using `((macofDet n).hasFDerivAt (fun i l => B y i l)).comp y hrows`. Establish `hc2 : HasFDerivAt (fun w => (B w).det) (((macofDet n).linearDeriv fun i l => B y i l).comp (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l)) y` using `hcomp`. Rewrite using `[hc2.fderiv]`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply, ContinuousLinearMap.pi_apply]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem macof_hasFDerivAt_det {n : ℕ} (B : V n → Matrix (Fin n) (Fin n) ℂ) (y : V n)
    (B' : Fin n → Fin n → (V n →L[ℝ] ℂ))
    (hB : ∀ i l, HasFDerivAt (fun w => B w i l) (B' i l) y) (v : V n) :
    fderiv ℝ (fun w => (B w).det) y v =
      ∑ i, ((B y).updateRow i (fun l => B' i l v)).det := by
  have hrows : HasFDerivAt (fun w => (fun i l => B w i l : Fin n → Fin n → ℂ))
      (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l) y :=
    hasFDerivAt_pi.2 fun i => hasFDerivAt_pi.2 fun l => hB i l
  have hcomp := ((macofDet n).hasFDerivAt (fun i l => B y i l)).comp y hrows
  have hc2 : HasFDerivAt (fun w => (B w).det)
      (((macofDet n).linearDeriv fun i l => B y i l).comp
        (ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun l => B' i l)) y := hcomp
  rw [hc2.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.linearDeriv_apply,
    ContinuousLinearMap.pi_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rfl

/- English proof (translation)
Establish `hB : (M.updateRow j e).updateRow i c = ((M.updateRow i e).updateRow j c).submatrix (Equiv.swap i j) id`. Use extensionality with `a b`. Simplify using `only [Matrix.submatrix_apply, id]`. Break down `eq_or_ne a i with rfl | ha` into its components or cases. Simplify using `[Matrix.updateRow_apply, h]`.

Break down `eq_or_ne a j with rfl | hb` into its components or cases. Simplify using `[Matrix.updateRow_apply, h, ha, Ne.symm h]`. Simplify using `[Matrix.updateRow_apply, ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]`. Rewrite using `[hB, Matrix.det_permute, Equiv.Perm.sign_swap h]`. Simplify using the standard rewrite rules.
-/
theorem macof_swap {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) {i j : Fin n} (h : i ≠ j)
    (e c : Fin n → ℂ) :
    ((M.updateRow i e).updateRow j c).det = -((M.updateRow j e).updateRow i c).det := by
  have hB : (M.updateRow j e).updateRow i c =
      ((M.updateRow i e).updateRow j c).submatrix (Equiv.swap i j) id := by
    ext a b
    simp only [Matrix.submatrix_apply, id]
    rcases eq_or_ne a i with rfl | ha
    · simp [Matrix.updateRow_apply, h]
    rcases eq_or_ne a j with rfl | hb
    · simp [Matrix.updateRow_apply, h, ha, Ne.symm h]
    · simp [Matrix.updateRow_apply, ha, hb, Equiv.swap_apply_of_ne_of_ne ha hb]
  rw [hB, Matrix.det_permute, Equiv.Perm.sign_swap h]
  simp

/- English proof (translation)
Establish `hGa : ContDiffAt ℝ ∞ G y` using `hG.contDiffAt (hU.mem_nhds hy)`. Apply the tactic sequence `have hsym := hGa.isSymmSndFDerivAt (by first | (simp; norm_cast) | simp | norm_cast)`. Apply the tactic sequence `have hD2 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) y) y := ((hGa.fderiv_right (m := 1) (by first | norm_cast | simp)).differentiableAt (by first | simp | decide)).hasFDerivAt`. Establish `key : ∀ (a : Fin n) (v : V n), fderiv ℝ (wd n a G) y v = (fderiv ℝ (fderiv ℝ G) y v (bas n a) - Complex.I * fderiv ℝ (fderiv ℝ G) y v (Complex.I • bas n a)) / 2`. Introduce `a v`.

Establish `h1 : HasFDerivAt (fun w => fderiv ℝ G w (bas n a)) ((fderiv ℝ (fderiv ℝ G) y).flip (bas n a)) y`. Establish `h0` using `hD2.clm_apply (hasFDerivAt_const (bas n a) y)`. Simplify using `using h0`. Establish `h2 : HasFDerivAt (fun w => fderiv ℝ G w (Complex.I • bas n a)) ((fderiv ℝ (fderiv ℝ G) y).flip (Complex.I • bas n a)) y`. Establish `h0` using `hD2.clm_apply (hasFDerivAt_const (Complex.I • bas n a) y)`.

Simplify using `using h0`. Establish `h3` using `(h1.sub (h2.const_mul Complex.I)).const_mul (2 : ℂ)⁻¹`. Establish `hwd : wd n a G = fun w => (fderiv ℝ G w (bas n a) - Complex.I * fderiv ℝ G w (Complex.I • bas n a)) / 2`. Use function extensionality and compare the values at `w`. Both sides reduce to the same expression.

Establish `h4 : HasFDerivAt (fun w => (fderiv ℝ G w (bas n a) - Complex.I * fderiv ℝ G w (Complex.I • bas n a)) / 2) ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ G) y).flip (bas n a) - Complex.I • (fderiv ℝ (fderiv ℝ G) y).flip (Complex.I • bas n a))) y`. Use `h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)` and prove the remaining obligations. Simplify using `only [Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hwd, h4.fderiv]`.

Simplify using `only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, ContinuousLinearMap.flip_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Use `show (fderiv ℝ (wd n i G) y (bas n j) - Complex.I * fderiv ℝ (wd n i G) y (Complex.I • bas n j)) / 2 = (fderiv ℝ (wd n j G) y (bas n i) - Complex.I * fderiv ℝ (wd n j G) y (Complex.I • bas n i)) / 2`. Rewrite using `[key i, key i, key j, key j, hsym (bas n j) (bas n i), hsym (bas n j) (Complex.I • bas n i), hsym (Complex.I • bas n j) (bas n i), hsym (Complex.I • bas n j) (Complex.I • bas n i)]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem wd_wd_comm_of_contDiffOn {n : ℕ} {U : Set (V n)} (hU : IsOpen U) {G : V n → ℂ}
    (hG : ContDiffOn ℝ ∞ G U) (i j : Fin n) {y : V n} (hy : y ∈ U) :
    wd n j (wd n i G) y = wd n i (wd n j G) y := by
  have hGa : ContDiffAt ℝ ∞ G y := hG.contDiffAt (hU.mem_nhds hy)
  have hsym := hGa.isSymmSndFDerivAt (by first | (simp; norm_cast) | simp | norm_cast)
  have hD2 : HasFDerivAt (fderiv ℝ G) (fderiv ℝ (fderiv ℝ G) y) y :=
    ((hGa.fderiv_right (m := 1) (by first | norm_cast | simp)).differentiableAt
      (by first | simp | decide)).hasFDerivAt
  have key : ∀ (a : Fin n) (v : V n), fderiv ℝ (wd n a G) y v =
      (fderiv ℝ (fderiv ℝ G) y v (bas n a) -
        Complex.I * fderiv ℝ (fderiv ℝ G) y v (Complex.I • bas n a)) / 2 := by
    intro a v
    have h1 : HasFDerivAt (fun w => fderiv ℝ G w (bas n a))
        ((fderiv ℝ (fderiv ℝ G) y).flip (bas n a)) y := by
      have h0 := hD2.clm_apply (hasFDerivAt_const (bas n a) y)
      simpa using h0
    have h2 : HasFDerivAt (fun w => fderiv ℝ G w (Complex.I • bas n a))
        ((fderiv ℝ (fderiv ℝ G) y).flip (Complex.I • bas n a)) y := by
      have h0 := hD2.clm_apply (hasFDerivAt_const (Complex.I • bas n a) y)
      simpa using h0
    have h3 := (h1.sub (h2.const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    have hwd : wd n a G = fun w =>
        (fderiv ℝ G w (bas n a) - Complex.I * fderiv ℝ G w (Complex.I • bas n a)) / 2 := by
      funext w
      rfl
    have h4 : HasFDerivAt (fun w =>
        (fderiv ℝ G w (bas n a) - Complex.I * fderiv ℝ G w (Complex.I • bas n a)) / 2)
        ((2 : ℂ)⁻¹ • ((fderiv ℝ (fderiv ℝ G) y).flip (bas n a) -
          Complex.I • (fderiv ℝ (fderiv ℝ G) y).flip (Complex.I • bas n a))) y := by
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
      simp only [Pi.sub_apply]
      ring
    rw [hwd, h4.fderiv]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  show (fderiv ℝ (wd n i G) y (bas n j) - Complex.I * fderiv ℝ (wd n i G) y (Complex.I • bas n j)) / 2 =
    (fderiv ℝ (wd n j G) y (bas n i) - Complex.I * fderiv ℝ (wd n j G) y (Complex.I • bas n i)) / 2
  rw [key i, key i, key j, key j, hsym (bas n j) (bas n i), hsym (bas n j) (Complex.I • bas n i),
    hsym (Complex.I • bas n j) (bas n i), hsym (Complex.I • bas n j) (Complex.I • bas n i)]
  ring

/- English proof (translation)
Introduce `U f hU hf y hy k`. Establish `hg : ContDiffOn ℝ ∞ (fun w' => (f w' : ℂ)) U` using `Complex.ofRealCLM.contDiff.comp_contDiffOn hf`. Establish `hent : ∀ i l, ContDiffOn ℝ ∞ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) U` using `fun i l => macof_wd_contDiffOn hU (macof_wdb_contDiffOn hU hg l) i`. Apply the tactic sequence `have hd : ∀ i l, DifferentiableAt ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y := fun i l => ((hent i l).contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | simp | decide)`. Establish `hwd : ∀ (j : Fin n) (F : V n → ℂ), wd n j F y = (fderiv ℝ F y (bas n j) - Complex.I * fderiv ℝ F y (Complex.I • bas n j)) / 2` using `fun j F => rfl`.

Establish `hdz : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n), (M.updateRow i 0).det = 0` using `fun M i => by rw [← macofRow_apply, map_zero]`. Take `⟨Z, hZ⟩ : ∃ Z : Fin n → Fin n → ℂ, ∀ i j, Z i j = if i = j then 0 else (((cHess n (fun w' => (f w' : ℂ)) y).updateRow j (Pi.single k 1)).updateRow i (fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y)).det` from `⟨_, fun _ _ => rfl⟩`. Establish `hterm : ∀ j, wd n j (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y = ∑ i, Z i j`. Introduce `j`. Establish `hfun : (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) = fun w => ((cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)).det`.

Use function extensionality and compare the values at `w`. Rewrite using `[Matrix.adjugate_apply]`. Establish `hB : ∀ i l, HasFDerivAt (fun w => ((cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)) i l) (if i = j then 0 else fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y) y`. Introduce `i l`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using `only [Matrix.updateRow_self, if_true]`. Conclude with `hasFDerivAt_const _ _`. Simplify using `only [Matrix.updateRow_ne hij, if_neg hij]`. Conclude with `(hd i l).hasFDerivAt`.

Establish `hdet` using `macof_hasFDerivAt_det (fun w => (cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)) y _ hB`. Apply the tactic sequence `try beta_reduce at hdet`. Rewrite using `[hfun, hwd, hdet, hdet, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hZ]`.

Distinguish the cases in `hij : i = j`. Simplify using `only [if_pos hij, ContinuousLinearMap.zero_apply]`. Simplify using `only [← Pi.zero_def, hdz]`. Apply the tactic sequence `first | ring | simp`. Simplify using `only [if_neg hij]`.

Rewrite using `[← macofRow_apply, ← macofRow_apply, ← macofRow_apply]`. Establish `hρ : (fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y) = (2 : ℂ)⁻¹ • ((fun l => fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y (bas n j)) - Complex.I • (fun l => fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y (Complex.I • bas n j)))`. Use function extensionality and compare the values at `l`. Simplify using `only [hwd, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hρ, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hanti : ∀ i j, Z i j = -Z j i`. Introduce `i j`. Rewrite using `[hZ, hZ]`.

Distinguish the cases in `hij : i = j`. Simplify using `[hij]`. Rewrite using `[if_neg hij, if_neg (Ne.symm hij)]`. Establish `hc : (fun l => wd n i (fun w => cHess n (fun w' => (f w' : ℂ)) w j l) y) = fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y`. Use function extensionality and compare the values at `l`.

Conclude with `wd_wd_comm_of_contDiffOn hU (macof_wdb_contDiffOn hU hg l) j i hy`. Rewrite using `[hc, macof_swap _ hij, neg_neg]`. Simplify using `only [hterm]`. Establish `hS : ∑ j, ∑ i, Z i j = -∑ j, ∑ i, Z i j`. Combine the equalities or inequalities in the displayed calculation.

Take the linear combination `hS / 2`.
-/
theorem macof_main (n : ℕ) : MACofStatement n := by
  intro U f hU hf y hy k
  have hg : ContDiffOn ℝ ∞ (fun w' => (f w' : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  have hent : ∀ i l, ContDiffOn ℝ ∞ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) U :=
    fun i l => macof_wd_contDiffOn hU (macof_wdb_contDiffOn hU hg l) i
  have hd : ∀ i l, DifferentiableAt ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y :=
    fun i l => ((hent i l).contDiffAt (hU.mem_nhds hy)).differentiableAt (by first | simp | decide)
  have hwd : ∀ (j : Fin n) (F : V n → ℂ), wd n j F y =
      (fderiv ℝ F y (bas n j) - Complex.I * fderiv ℝ F y (Complex.I • bas n j)) / 2 :=
    fun j F => rfl
  have hdz : ∀ (M : Matrix (Fin n) (Fin n) ℂ) (i : Fin n), (M.updateRow i 0).det = 0 :=
    fun M i => by rw [← macofRow_apply, map_zero]
  obtain ⟨Z, hZ⟩ : ∃ Z : Fin n → Fin n → ℂ, ∀ i j, Z i j = if i = j then 0 else
      (((cHess n (fun w' => (f w' : ℂ)) y).updateRow j (Pi.single k 1)).updateRow i
        (fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y)).det :=
    ⟨_, fun _ _ => rfl⟩
  have hterm : ∀ j, wd n j (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) y =
      ∑ i, Z i j := by
    intro j
    have hfun : (fun w => (cHess n (fun w' => (f w' : ℂ)) w).adjugate k j) =
        fun w => ((cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)).det := by
      funext w
      rw [Matrix.adjugate_apply]
    have hB : ∀ i l, HasFDerivAt
        (fun w => ((cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)) i l)
        (if i = j then 0 else fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y) y := by
      intro i l
      by_cases hij : i = j
      · subst hij
        simp only [Matrix.updateRow_self, if_true]
        exact hasFDerivAt_const _ _
      · simp only [Matrix.updateRow_ne hij, if_neg hij]
        exact (hd i l).hasFDerivAt
    have hdet := macof_hasFDerivAt_det
      (fun w => (cHess n (fun w' => (f w' : ℂ)) w).updateRow j (Pi.single k 1)) y _ hB
    try beta_reduce at hdet
    rw [hfun, hwd, hdet, hdet, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hZ]
    by_cases hij : i = j
    · simp only [if_pos hij, ContinuousLinearMap.zero_apply]
      simp only [← Pi.zero_def, hdz]
      first | ring | simp
    · simp only [if_neg hij]
      rw [← macofRow_apply, ← macofRow_apply, ← macofRow_apply]
      have hρ : (fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y) =
          (2 : ℂ)⁻¹ • ((fun l => fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y (bas n j)) -
            Complex.I • (fun l => fderiv ℝ (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y
              (Complex.I • bas n j))) := by
        funext l
        simp only [hwd, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [hρ, map_smul, map_sub, map_smul, smul_eq_mul, smul_eq_mul]
      ring
  have hanti : ∀ i j, Z i j = -Z j i := by
    intro i j
    rw [hZ, hZ]
    by_cases hij : i = j
    · simp [hij]
    · rw [if_neg hij, if_neg (Ne.symm hij)]
      have hc : (fun l => wd n i (fun w => cHess n (fun w' => (f w' : ℂ)) w j l) y) =
          fun l => wd n j (fun w => cHess n (fun w' => (f w' : ℂ)) w i l) y := by
        funext l
        exact wd_wd_comm_of_contDiffOn hU (macof_wdb_contDiffOn hU hg l) j i hy
      rw [hc, macof_swap _ hij, neg_neg]
  simp only [hterm]
  have hS : ∑ j, ∑ i, Z i j = -∑ j, ∑ i, Z i j := by
    calc ∑ j, ∑ i, Z i j = ∑ j, ∑ i, -Z j i :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => hanti i j
      _ = -∑ j, ∑ i, Z j i := by simp only [Finset.sum_neg_distrib]
      _ = -∑ j, ∑ i, Z i j := by rw [Finset.sum_comm]
  linear_combination hS / 2

end

/- English proof (translation)
The claim follows from `macof_main n`.
-/
theorem maCof (n : ℕ) : MACofStatement n := macof_main n

end ReciprocityTheory.L2DbarEstimates.I
