import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.DetSubMapConj

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf

open Matrix NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.L2DbarEstimates ReciprocityTheory.AnForm Filter Topology

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

/- English proof (translation)
Unfold `Data.nfac`. Establish `hpos : ∀ τ (i : Fin r), 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖` using `fun τ i => norm_pos_iff.2 (div_ne_zero (hx _ _) (hx _ _))`. Rewrite using `[Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hpos τ i) _).ne'), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hpos τ i) _).ne'), Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Real.log_rpow (hpos τ i), norm_div, Real.log_div (norm_ne_zero_iff.2 (hx _ _)) (norm_ne_zero_iff.2 (hx _ _))]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem neg2log_nfac (la : Wt X.Ψ r) (x : Frame X.Ψ r) (hx : ∀ τ i, dmin X.Gm x τ i ≠ 0) :
    -2 * Real.log (X.nfac la x) = ∑ τ, ∑ i : Fin r, (la τ i : ℝ) *
      (Real.log ‖dmin X.Gm x τ i.succ‖ - Real.log ‖dmin X.Gm x τ i.castSucc‖) := by
  unfold Data.nfac
  have hpos : ∀ τ (i : Fin r), 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
    fun τ i => norm_pos_iff.2 (div_ne_zero (hx _ _) (hx _ _))
  rw [Real.log_prod (fun τ _ => (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hpos τ i) _).ne'),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Real.log_prod (fun i _ => (Real.rpow_pos_of_pos (hpos τ i) _).ne'), Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.log_rpow (hpos τ i), norm_div, Real.log_div (norm_ne_zero_iff.2 (hx _ _)) (norm_ne_zero_iff.2 (hx _ _))]
  ring

/- English proof (translation)
Unfold `levi`. Establish `h : (fderiv ℝ fun _ : ι → ℂ => c) = fun _ => 0`. Use function extensionality and compare the values at `x`. Conclude with `fderiv_const_apply c`. Rewrite using `[h]`.

Simplify using the standard rewrite rules.
-/
theorem levi_const {ι : Type} [Fintype ι] (c : ℝ) (z w : ι → ℂ) : levi (fun _ => c) z w = 0 := by
  unfold levi
  have h : (fderiv ℝ fun _ : ι → ℂ => c) = fun _ => 0 := by
    funext x
    exact fderiv_const_apply c
  rw [h]
  simp

/- English proof (translation)
Rewrite using `[levi_add_smul c contDiffAt_const hf, levi_const, zero_add]`.
-/
theorem levi_affine {ι : Type} [Fintype ι] (K c : ℝ) (f : (ι → ℂ) → ℝ) (z w : ι → ℂ)
    (hf : ContDiffAt ℝ 2 f z) : levi (fun v => K + c * f v) z w = c * levi f z w := by
  rw [levi_add_smul c contDiffAt_const hf, levi_const, zero_add]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [levi_const]`. Consider the case `insert a s ha ih`. Establish `hs : ContDiffAt ℝ 2 (fun v => ∑ j ∈ s, F j v) z` using `ContDiffAt.sum fun j hj => hF j (Finset.mem_insert_of_mem hj)`. Establish `e : (fun v => ∑ j ∈ insert a s, F j v) = fun v => (∑ j ∈ s, F j v) + 1 * F a v`.

Use function extensionality and compare the values at `v`. Rewrite using `[Finset.sum_insert ha]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, levi_add_smul 1 hs (hF a (Finset.mem_insert_self a s)), ih fun j hj => hF j (Finset.mem_insert_of_mem hj), Finset.sum_insert ha]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem levi_finset_sum {ι κ : Type} [Fintype ι] (s : Finset κ) (F : κ → (ι → ℂ) → ℝ) (z w : ι → ℂ)
    (hF : ∀ j ∈ s, ContDiffAt ℝ 2 (F j) z) :
    levi (fun v => ∑ j ∈ s, F j v) z w = ∑ j ∈ s, levi (F j) z w := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [levi_const]
  | insert a s ha ih =>
    have hs : ContDiffAt ℝ 2 (fun v => ∑ j ∈ s, F j v) z :=
      ContDiffAt.sum fun j hj => hF j (Finset.mem_insert_of_mem hj)
    have e : (fun v => ∑ j ∈ insert a s, F j v) = fun v => (∑ j ∈ s, F j v) + 1 * F a v := by
      funext v; rw [Finset.sum_insert ha]; ring
    rw [e, levi_add_smul 1 hs (hF a (Finset.mem_insert_self a s)),
      ih fun j hj => hF j (Finset.mem_insert_of_mem hj), Finset.sum_insert ha]
    ring

/- English proof (translation)
Establish `htri : U.BlockTriangular id` using `fun a c h => hU a c h`. Establish `hdiag : ∀ a, U a a ≠ 0`. Introduce `a ha`. Apply `hd` to reduce the goal to its premises. Rewrite using `[Matrix.det_of_upperTriangular htri]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ a) ha`. Establish `htri2 : (U.submatrix (Fin.castLE hm) (Fin.castLE hm)).BlockTriangular id`. Introduce `a c h`. Conclude with `hU _ _ (Fin.lt_def.mpr (by simp only [Fin.coe_castLE]; exact Fin.lt_def.mp h))`. Rewrite using `[Matrix.det_of_upperTriangular htri2]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun a _ => hdiag _`.
-/
theorem det_lead_ne (U : Matrix (Fin r) (Fin r) ℂ) (hU : ∀ a c : Fin r, c < a → U a c = 0) (hd : U.det ≠ 0)
    {m : ℕ} (hm : m ≤ r) : (U.submatrix (Fin.castLE hm) (Fin.castLE hm)).det ≠ 0 := by
  have htri : U.BlockTriangular id := fun a c h => hU a c h
  have hdiag : ∀ a, U a a ≠ 0 := by
    intro a ha
    apply hd
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_zero (Finset.mem_univ a) ha
  have htri2 : (U.submatrix (Fin.castLE hm) (Fin.castLE hm)).BlockTriangular id := by
    intro a c h
    exact hU _ _ (Fin.lt_def.mpr (by simp only [Fin.coe_castLE]; exact Fin.lt_def.mp h))
  rw [Matrix.det_of_upperTriangular htri2]
  exact Finset.prod_ne_zero_iff.mpr fun a _ => hdiag _

section Line

variable (x0 b : Frame X.Ψ r) (z u : V (nd X))

def fk (τ : X.Ψ) (k : Fin (r + 1)) : (Fin 1 → ℂ) → ℝ :=
  fY (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ)

def cB (τ : X.Ψ) (k : Fin (r + 1)) : ℝ :=
  Real.log (‖((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
    (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det‖ ^ 2)

variable {X x0 b z u}

/- English proof (translation)
Rewrite using `[dmin_line X x0 b hb z u τ (hgram τ) (v 0) k, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]`. Establish `hg : (Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0)).det.im = 0`. Establish `h` using `congrArg Matrix.det (Gz_herm (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0))`. Rewrite `h` using `[Matrix.det_conjTranspose]`. Conclude with `Complex.conj_eq_iff_im.1 h`.

Establish `hn : ‖(Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0)).det‖ = |fk X b z u τ k v|`. Unfold `fk fY`. Conclude with `(Complex.abs_re_eq_norm.2 hg).symm`. Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dmin_line_norm (hb : b ∈ Bor X.Ψ r) (hgram : ∀ τ, gram τ.1 X.Gm (mat (rmul (cpt X x0 z) b) τ) =
      diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (v : Fin 1 → ℂ) (τ : X.Ψ) (k : Fin (r + 1)) :
    ‖dmin X.Gm (cpt X x0 (z + (v 0) • u)) τ k‖ =
      ‖((mat b τ)⁻¹.submatrix (Fin.castLE (Nat.le_of_lt_succ k.isLt))
        (Fin.castLE (Nat.le_of_lt_succ k.isLt))).det‖ ^ 2 * |fk X b z u τ k v| := by
  rw [dmin_line X x0 b hb z u τ (hgram τ) (v 0) k, norm_mul, norm_mul, Complex.norm_conj, Complex.norm_conj]
  have hg : (Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0)).det.im = 0 := by
    have h := congrArg Matrix.det (Gz_herm (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0))
    rw [Matrix.det_conjTranspose] at h
    exact Complex.conj_eq_iff_im.1 h
  have hn : ‖(Gz (Nat.le_of_lt_succ k.isLt) (Dsg X) (Yd X b z u τ) (v 0)).det‖ = |fk X b z u τ k v| := by
    unfold fk fY
    exact (Complex.abs_re_eq_norm.2 hg).symm
  rw [hn]
  ring

end Line

end ReciprocityTheory.ChartRestriction.G.AR.Inst.CurvPf
