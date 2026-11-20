import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.InverseLineDerivatives.HasDerivAtRmOne

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxd2

open PositivityTheory.RgTw (Mat)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

/- English proof (translation)
Use `contDiff_pi.2 fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = j`. Substitute `hk` using the available equality. Establish `e : (fun x : Mat n => x.updateRow k v k) = fun _ => v` using `by funext x; simp [Matrix.updateRow_apply]`. Rewrite using `[e]`.

Conclude with `contDiff_const`. Establish `e : (fun x : Mat n => x.updateRow j v k) = fun x : Mat n => (x : Fin n → Fin n → ℂ) k`. Use function extensionality and compare the values at `x`. Simplify using `[Matrix.updateRow_apply, hk]`. Rewrite using `[e]`.

Conclude with `contDiff_apply ℝ (Fin n → ℂ) k`.
-/
theorem updateRow_smooth (j : Fin n) (v : Fin n → ℂ) : ContDiff ℝ ∞ (fun x : Mat n => x.updateRow j v) := by
  refine contDiff_pi.2 fun k => ?_
  by_cases hk : k = j
  · subst hk
    have e : (fun x : Mat n => x.updateRow k v k) = fun _ => v := by funext x; simp [Matrix.updateRow_apply]
    rw [e]; exact contDiff_const
  · have e : (fun x : Mat n => x.updateRow j v k) = fun x : Mat n => (x : Fin n → Fin n → ℂ) k := by
      funext x; simp [Matrix.updateRow_apply, hk]
    rw [e]; exact contDiff_apply ℝ (Fin n → ℂ) k

/- English proof (translation)
Use `contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_` and prove the remaining obligations. Establish `e : (fun x : Mat n => x.adjugate i j) = fun x : Mat n => (x.updateRow j (Pi.single i 1)).det`. Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.adjugate_apply]`. Rewrite using `[e]`.

Conclude with `Cxc.det_smooth.comp (updateRow_smooth j _)`.
-/
theorem adjugate_smooth : ContDiff ℝ ∞ (fun x : Mat n => x.adjugate) := by
  refine contDiff_pi.2 fun i => contDiff_pi.2 fun j => ?_
  have e : (fun x : Mat n => x.adjugate i j) = fun x : Mat n => (x.updateRow j (Pi.single i 1)).det := by
    funext x; rw [Matrix.adjugate_apply]
  rw [e]
  exact Cxc.det_smooth.comp (updateRow_smooth j _)

/- English proof (translation)
Establish `h : ContDiffOn ℝ ∞ (fun x : Mat n => Matrix.of fun i j => x.det ^ (-1 : ℤ) * x.adjugate i j) (GLs n)`. Use `contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_` and prove the remaining obligations. Conclude with `(Cxc.detPow_smooth (-1)).mul ((contDiff_apply_apply ℝ ℂ i j).comp adjugate_smooth).contDiffOn`. Use `h.congr fun x hx => ?_` and prove the remaining obligations. Use extensionality with `i j`.

Rewrite using `[Matrix.inv_def, Ring.inverse_eq_inv]`. Simplify using `[_root_.zpow_neg_one]`.
-/
theorem inv_smooth : ContDiffOn ℝ ∞ (fun x : Mat n => x⁻¹) (GLs n) := by
  have h : ContDiffOn ℝ ∞ (fun x : Mat n => Matrix.of fun i j => x.det ^ (-1 : ℤ) * x.adjugate i j) (GLs n) := by
    refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => ?_
    exact (Cxc.detPow_smooth (-1)).mul ((contDiff_apply_apply ℝ ℂ i j).comp adjugate_smooth).contDiffOn
  refine h.congr fun x hx => ?_
  ext i j
  rw [Matrix.inv_def, Ring.inverse_eq_inv]
  simp [_root_.zpow_neg_one]

def cTL : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun A => Aᴴ
      map_add' := fun A B => Matrix.conjTranspose_add A B
      map_smul' := fun r A => by simp [Matrix.conjTranspose_smul] }

/- English proof (translation)
Establish `hu : IsUnit x.det` using `isUnit_iff_ne_zero.2 hx`. Rewrite using `[Matrix.det_nonsing_inv, Ring.inverse_eq_inv]`. Conclude with `inv_ne_zero hx`.
-/
theorem det_inv_ne {x : Mat n} (hx : x ∈ GLs n) : (x⁻¹).det ≠ 0 := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.2 hx
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero hx

/- English proof (translation)
Use `show ((x⁻¹)ᴴ).det ≠ 0`. Rewrite using `[Matrix.det_conjTranspose]`. Conclude with `(star_ne_zero).2 (det_inv_ne hx)`.
-/
theorem mem_theta {x : Mat n} (hx : x ∈ GLs n) : (x⁻¹)ᴴ ∈ GLs n := by
  show ((x⁻¹)ᴴ).det ≠ 0
  rw [Matrix.det_conjTranspose]
  exact (star_ne_zero).2 (det_inv_ne hx)

/- English proof (translation)
Establish `h` using `(inv_smooth.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)`. Conclude with `cTL.differentiableAt.comp x h`.
-/
theorem theta_diff {x : Mat n} (hx : x ∈ GLs n) : DifferentiableAt ℝ (fun y : Mat n => (y⁻¹)ᴴ) x := by
  have h := (inv_smooth.contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
  exact cTL.differentiableAt.comp x h

/- English proof (translation)
Establish `hP2 : ∀ i k, HasDerivAt (fun t => P t i k) (P' i k) 0` using `fun i k => hasDerivAt_pi.1 (hasDerivAt_pi.1 hP i) k`. Establish `hQ2 : ∀ k j, HasDerivAt (fun t => Q t k j) (Q' k j) 0` using `fun k j => hasDerivAt_pi.1 (hasDerivAt_pi.1 hQ k) j`. Use `hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_` and prove the remaining obligations. Establish `h` using `HasDerivAt.sum (u := Finset.univ) fun k _ => (hP2 i k).mul (hQ2 k j)`. Simplify using `only [Matrix.mul_apply, Matrix.add_apply]`.

Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Simplify using `[Finset.sum_apply]`. Simplify using `[Finset.sum_add_distrib, mul_comm]`.
-/
theorem hasDerivAt_mat_mul {m : Type} [Fintype m] [DecidableEq m] {P Q : ℝ → Matrix m m ℂ} {P' Q' : Matrix m m ℂ}
    (hP : HasDerivAt P P' 0) (hQ : HasDerivAt Q Q' 0) :
    HasDerivAt (fun t => P t * Q t) (P' * Q 0 + P 0 * Q') 0 := by
  have hP2 : ∀ i k, HasDerivAt (fun t => P t i k) (P' i k) 0 := fun i k =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hP i) k
  have hQ2 : ∀ k j, HasDerivAt (fun t => Q t k j) (Q' k j) 0 := fun k j =>
    hasDerivAt_pi.1 (hasDerivAt_pi.1 hQ k) j
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => ?_
  have h := HasDerivAt.sum (u := Finset.univ) fun k _ => (hP2 i k).mul (hQ2 k j)
  simp only [Matrix.mul_apply, Matrix.add_apply]
  convert h using 1
  · funext t; simp [Finset.sum_apply]
  · simp [Finset.sum_add_distrib, mul_comm]

/- English proof (translation)
Establish `hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0`. Establish `h` using `((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)`. Rewrite `h` using `[one_smul]`. Conclude with `h`. Establish `h1 : (1 : Mat n) ∈ GLs n` using `by simp [GLs]`.

Establish `hd : DifferentiableAt ℝ (fun x : Mat n => x⁻¹) (1 : Mat n)` using `(inv_smooth.contDiffAt (isOpen_GLs.mem_nhds h1)).differentiableAt (by simp)`. Establish `hu : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (fderiv ℝ (fun x : Mat n => x⁻¹) 1 X) 0`. Use `hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)` as an intermediate fact. Conclude with `this`. Establish `hprod` using `hasDerivAt_mat_mul hc hu`.

Establish `hconst : (fun t : ℝ => (1 + t • X) * (1 + t • X)⁻¹) =ᶠ[nhds 0] fun _ => (1 : Mat n)` using `by filter_upwards [eventually_det X] with t ht`. Conclude with `Matrix.mul_nonsing_inv _ ht`. Establish `h0` using `(hasDerivAt_const (0 : ℝ) (1 : Mat n)).congr_of_eventuallyEq hconst`. Establish `e` using `hprod.unique h0`. Simplify using `only [zero_smul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul] at e`.

Establish `e2 : fderiv ℝ (fun x : Mat n => x⁻¹) 1 X = -X`. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm]`. Conclude with `e`. Rewrite `hu` using `[e2]`. Then use the resulting hypothesis.
-/
theorem hasDerivAt_inv_line (X : Mat n) : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (-X) 0 := by
  have hc : HasDerivAt (fun t : ℝ => (1 : Mat n) + t • X) X 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (1 : Mat n)
    rw [one_smul] at h
    exact h
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have hd : DifferentiableAt ℝ (fun x : Mat n => x⁻¹) (1 : Mat n) :=
    (inv_smooth.contDiffAt (isOpen_GLs.mem_nhds h1)).differentiableAt (by simp)
  have hu : HasDerivAt (fun t : ℝ => (1 + t • X)⁻¹) (fderiv ℝ (fun x : Mat n => x⁻¹) 1 X) 0 := by
    have := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
    exact this
  have hprod := hasDerivAt_mat_mul hc hu
  have hconst : (fun t : ℝ => (1 + t • X) * (1 + t • X)⁻¹) =ᶠ[nhds 0] fun _ => (1 : Mat n) := by
    filter_upwards [eventually_det X] with t ht
    exact Matrix.mul_nonsing_inv _ ht
  have h0 := (hasDerivAt_const (0 : ℝ) (1 : Mat n)).congr_of_eventuallyEq hconst
  have e := hprod.unique h0
  simp only [zero_smul, add_zero, inv_one, Matrix.mul_one, Matrix.one_mul] at e
  have e2 : fderiv ℝ (fun x : Mat n => x⁻¹) 1 X = -X := by
    rw [eq_neg_iff_add_eq_zero, add_comm]; exact e
  rwa [e2] at hu

/- English proof (translation)
Establish `hc : HasDerivAt (fun t : ℝ => ((1 + t • X)⁻¹)ᴴ) (-Xᴴ) 0`. Use `cTL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_inv_line X)` as an intermediate fact. Conclude with `this.congr_deriv (Matrix.conjTranspose_neg X)`. Establish `h1 : (1 : Mat n) ∈ GLs n` using `by simp [GLs]`. Establish `h` using `(rm_diff lam h1).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)`.

Conclude with `h.congr_deriv (hD n lam hlam _)`.
-/
theorem hasDerivAt_rm_theta (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (X : Mat n) :
    HasDerivAt (fun t : ℝ => Rm lam ((1 + t • X)⁻¹)ᴴ) (∑ a, ∑ b, (-Xᴴ) a b • At lam a b) 0 := by
  have hc : HasDerivAt (fun t : ℝ => ((1 + t • X)⁻¹)ᴴ) (-Xᴴ) 0 := by
    have := cTL.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_inv_line X)
    exact this.congr_deriv (Matrix.conjTranspose_neg X)
  have h1 : (1 : Mat n) ∈ GLs n := by simp [GLs]
  have h := (rm_diff lam h1).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hc (by simp)
  exact h.congr_deriv (hD n lam hlam _)

/- English proof (translation)
Establish `hdf : DifferentiableAt ℝ (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x`. Establish `: (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) = entL 1 N i j ∘ Rm lam ∘ fun y : Mat n => (y⁻¹)ᴴ`. Use function extensionality and compare the values at `y`. Simplify using `[entL_apply]`. Rewrite using `[this]`.

Conclude with `(entL 1 N i j).differentiableAt.comp x ((rm_diff lam (mem_theta hx)).comp x (theta_diff hx))`. Establish `h1` using `hasDerivAt_line hdf X`. Establish `h2 : HasDerivAt (fun t : ℝ => entL (Rm lam (x⁻¹)ᴴ) N i j (Rm lam ((1 + t • X)⁻¹)ᴴ)) (entL (Rm lam (x⁻¹)ᴴ) N i j (∑ a, ∑ b, (-Xᴴ) a b • At lam a b)) 0` using `(entL (Rm lam (x⁻¹)ᴴ) N i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rm_theta lam hD hlam X)`. Establish `hxu : IsUnit ((x⁻¹)ᴴ).det` using `isUnit_iff_ne_zero.2 (mem_theta hx)`. Establish `h3 : (fun t : ℝ => (Rm lam ((x * (1 + t • X))⁻¹)ᴴ * N) i j) =ᶠ[nhds 0] fun t : ℝ => entL (Rm lam (x⁻¹)ᴴ) N i j (Rm lam ((1 + t • X)⁻¹)ᴴ)` using `by filter_upwards [eventually_det X] with t ht`.

Establish `ht' : IsUnit (((1 + t • X)⁻¹)ᴴ).det`. Rewrite using `[Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]`. Conclude with `(isUnit_iff_ne_zero.2 (star_ne_zero.2 (inv_ne_zero (isUnit_iff_ne_zero.1 ht))))`. Rewrite using `[entL_apply, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Cxc.rm_mul lam _ _ hxu ht']`. Conclude with `h1.unique (h2.congr_of_eventuallyEq h3)`.
-/
theorem rd_anti (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (X : Mat n) :
    Rd X (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x = (Rm lam (x⁻¹)ᴴ * (∑ a, ∑ b, (-Xᴴ) a b • At lam a b) * N) i j := by
  have hdf : DifferentiableAt ℝ (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x := by
    have : (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) = entL 1 N i j ∘ Rm lam ∘ fun y : Mat n => (y⁻¹)ᴴ := by
      funext y; simp [entL_apply]
    rw [this]
    exact (entL 1 N i j).differentiableAt.comp x ((rm_diff lam (mem_theta hx)).comp x (theta_diff hx))
  have h1 := hasDerivAt_line hdf X
  have h2 : HasDerivAt (fun t : ℝ => entL (Rm lam (x⁻¹)ᴴ) N i j (Rm lam ((1 + t • X)⁻¹)ᴴ))
      (entL (Rm lam (x⁻¹)ᴴ) N i j (∑ a, ∑ b, (-Xᴴ) a b • At lam a b)) 0 :=
    (entL (Rm lam (x⁻¹)ᴴ) N i j).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rm_theta lam hD hlam X)
  have hxu : IsUnit ((x⁻¹)ᴴ).det := isUnit_iff_ne_zero.2 (mem_theta hx)
  have h3 : (fun t : ℝ => (Rm lam ((x * (1 + t • X))⁻¹)ᴴ * N) i j) =ᶠ[nhds 0]
      fun t : ℝ => entL (Rm lam (x⁻¹)ᴴ) N i j (Rm lam ((1 + t • X)⁻¹)ᴴ) := by
    filter_upwards [eventually_det X] with t ht
    have ht' : IsUnit (((1 + t • X)⁻¹)ᴴ).det := by
      rw [Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
      exact (isUnit_iff_ne_zero.2 (star_ne_zero.2 (inv_ne_zero (isUnit_iff_ne_zero.1 ht))))
    rw [entL_apply, Matrix.mul_inv_rev, Matrix.conjTranspose_mul, Cxc.rm_mul lam _ _ hxu ht']
  exact h1.unique (h2.congr_of_eventuallyEq h3)

/- English proof (translation)
Rewrite using `[Matrix.conjTranspose_single]`. Simplify using `only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]`. Rewrite using `[sum_single (lam := lam) 0 b a _ A]`.
-/
theorem sum_single_neg {lam : Fin n → ℤ} (a b : Fin n) (z : ℂ) (A : Fin n → Fin n → Matrix (Jd n lam) (Jd n lam) ℂ) :
    ∑ c, ∑ d, (-(Matrix.single a b z : Mat n)ᴴ) c d • A c d = (-star z) • A b a := by
  rw [Matrix.conjTranspose_single]
  simp only [Matrix.neg_apply, neg_smul, Finset.sum_neg_distrib]
  rw [sum_single (lam := lam) 0 b a _ A]

/- English proof (translation)
Establish `e1` using `rd_anti lam hD hlam N i j hx (Matrix.single a b 1)`. Establish `e2` using `rd_anti lam hD hlam N i j hx (Matrix.single a b Complex.I)`. Rewrite `e1` using `[sum_single_neg a b 1 (At lam)]`. Rewrite `e2` using `[sum_single_neg a b Complex.I (At lam)]`. Simplify using `only [Eu, Pi.add_apply, Pi.smul_apply, e1, e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]`.

Apply the tactic sequence `cases s <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring`.
-/
theorem eu_anti (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (N : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) {x : Mat n} (hx : x ∈ GLs n) (s : Bool) (a b : Fin n) :
    Eu s a b (fun y => (Rm lam (y⁻¹)ᴴ * N) i j) x = if s then 0 else (Rm lam (x⁻¹)ᴴ * -At lam b a * N) i j := by
  have e1 := rd_anti lam hD hlam N i j hx (Matrix.single a b 1)
  have e2 := rd_anti lam hD hlam N i j hx (Matrix.single a b Complex.I)
  rw [sum_single_neg a b 1 (At lam)] at e1
  rw [sum_single_neg a b Complex.I (At lam)] at e2
  simp only [Eu, Pi.add_apply, Pi.smul_apply, e1, e2, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_neg, Matrix.neg_mul, Matrix.neg_apply]
  cases s <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def Bt (lam : Fin n → ℤ) : Matrix (Fin n) (Fin n) (Matrix (Jd n lam) (Jd n lam) ℂ) := Matrix.of fun a b => -(At lam b a)

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `a b y _`. Simplify using `only [Epow, pow_zero, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Consider the case `succ m ih`. Introduce `a b y hy`. Simplify using `only [Epow, Finset.sum_apply]`. Establish `e : ∀ c, Eu false a c (Epow false m c b fun y => (Rm lam (y⁻¹)ᴴ * M) i j) y = (Rm lam (y⁻¹)ᴴ * Bt lam a c * ((Bt lam ^ m) c b * M)) i j`. Introduce `c`.

Establish `hev : (Epow false m c b fun y => (Rm lam (y⁻¹)ᴴ * M) i j) =ᶠ[nhds y] fun y => (Rm lam (y⁻¹)ᴴ * ((Bt lam ^ m) c b * M)) i j` using `by filter_upwards [isOpen_GLs.mem_nhds hy] with z hz`. Rewrite using `[ih c b hz]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[eu_congr hev, eu_anti lam hD hlam _ i j hy]`. Simplify using `[Bt, Matrix.mul_assoc]`.

Simplify using `only [e]`. Establish `hp : (Bt lam ^ (m + 1)) a b = ∑ c, Bt lam a c * (Bt lam ^ m) c b` using `by rw [pow_succ', Matrix.mul_apply]`. Use `show ∑ c, _ = (Rm lam (y⁻¹)ᴴ * (Bt lam ^ (m + 1)) a b * M) i j`. Rewrite using `[hp, Matrix.mul_sum, Finset.sum_mul, Matrix.sum_apply]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.mul_assoc]`.
-/
theorem epow_anti (lam : Fin n → ℤ) (hD : AtDer) (hlam : Antitone lam) (M : Matrix (Jd n lam) (Jd n lam) ℂ)
    (i j : Jd n lam) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow false m a b (fun y => (Rm lam (y⁻¹)ᴴ * M) i j))
      (fun y => (Rm lam (y⁻¹)ᴴ * (Bt lam ^ m) a b * M) i j) (GLs n) := by
  induction m with
  | zero =>
    intro a b y _
    simp only [Epow, pow_zero, Matrix.one_apply]
    split_ifs <;> simp
  | succ m ih =>
    intro a b y hy
    simp only [Epow, Finset.sum_apply]
    have e : ∀ c, Eu false a c (Epow false m c b fun y => (Rm lam (y⁻¹)ᴴ * M) i j) y =
        (Rm lam (y⁻¹)ᴴ * Bt lam a c * ((Bt lam ^ m) c b * M)) i j := by
      intro c
      have hev : (Epow false m c b fun y => (Rm lam (y⁻¹)ᴴ * M) i j) =ᶠ[nhds y]
          fun y => (Rm lam (y⁻¹)ᴴ * ((Bt lam ^ m) c b * M)) i j := by
        filter_upwards [isOpen_GLs.mem_nhds hy] with z hz
        rw [ih c b hz]
        simp only [Matrix.mul_assoc]
      rw [eu_congr hev, eu_anti lam hD hlam _ i j hy]
      simp [Bt, Matrix.mul_assoc]
    simp only [e]
    have hp : (Bt lam ^ (m + 1)) a b = ∑ c, Bt lam a c * (Bt lam ^ m) c b := by rw [pow_succ', Matrix.mul_apply]
    show ∑ c, _ = (Rm lam (y⁻¹)ᴴ * (Bt lam ^ (m + 1)) a b * M) i j
    rw [hp, Matrix.mul_sum, Finset.sum_mul, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `n lam hlam M i j g hg`. Use `⟨fun m => ?_, fun a b => by rw [eu_anti lam hD hlam M i j hg true a b]; rfl⟩` and prove the remaining obligations. Simplify using `only [gel, Finset.sum_apply]`. Rewrite using `[Finset.sum_congr rfl fun a _ => epow_anti lam hD hlam M i j m a a hg]`. Establish `e : ∑ a, (Rm lam (g⁻¹)ᴴ * (Bt lam ^ m) a a * M) i j = (Rm lam (g⁻¹)ᴴ * (Bt lam ^ m).trace * M) i j`.

Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]`. Rewrite using `[e]`. Establish `hB : (Bt lam ^ m).trace = GlobalTheory.Dec.gelfVal (infOf lam false) m • (1 : Matrix (Jd n lam) (Jd n lam) ℂ)` using `hT n lam hlam m`. Rewrite using `[hB]`. Simplify using `[Matrix.mul_smul, Matrix.smul_mul]`.
-/
theorem rmAnti_of (hT : AtTraceT) (hD : AtDer) : RmAnti := by
  intro n lam hlam M i j g hg
  refine ⟨fun m => ?_, fun a b => by rw [eu_anti lam hD hlam M i j hg true a b]; rfl⟩
  simp only [gel, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => epow_anti lam hD hlam M i j m a a hg]
  have e : ∑ a, (Rm lam (g⁻¹)ᴴ * (Bt lam ^ m) a a * M) i j = (Rm lam (g⁻¹)ᴴ * (Bt lam ^ m).trace * M) i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_sum, Matrix.sum_mul, Matrix.sum_apply]
  rw [e]
  have hB : (Bt lam ^ m).trace = GlobalTheory.Dec.gelfVal (infOf lam false) m • (1 : Matrix (Jd n lam) (Jd n lam) ℂ) :=
    hT n lam hlam m
  rw [hB]
  simp [Matrix.mul_smul, Matrix.smul_mul]

end PositivityTheory.RgBcC.Cxd2
