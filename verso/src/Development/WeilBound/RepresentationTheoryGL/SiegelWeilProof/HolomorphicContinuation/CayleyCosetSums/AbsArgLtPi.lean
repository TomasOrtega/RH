import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockMulUnipotentDomain

noncomputable section

open Matrix Filter Topology Set

namespace PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs

variable {n : ℕ}

/- English proof (translation)
Rewrite using `[abs_lt]`. Conclude with `⟨Complex.neg_pi_lt_arg P, lt_of_le_of_ne (Complex.arg_le_pi P) (Complex.slitPlane_arg_ne_pi hP)⟩`.
-/
theorem abs_arg_lt_pi {P : ℂ} (hP : P ∈ Complex.slitPlane) : |P.arg| < Real.pi := by
  rw [abs_lt]
  exact ⟨Complex.neg_pi_lt_arg P, lt_of_le_of_ne (Complex.arg_le_pi P) (Complex.slitPlane_arg_ne_pi hP)⟩

/- English proof (translation)
Establish `hP0 : P ≠ 0` using `Complex.slitPlane_ne_zero hP`. Establish `hPpi` using `abs_arg_lt_pi hP`. Establish `hpos : 0 ≤ Real.pi - |P.arg|` using `by linarith`. Establish `h1 : P.arg + a.arg ∈ Ioc (-Real.pi) Real.pi`. Use `abs_add_le P.arg a.arg` as an intermediate fact.

Prove the components needed by the constructor for the conclusion. Combine the linear relations using `[neg_abs_le (P.arg + a.arg)]`. Combine the linear relations using `[le_abs_self (P.arg + a.arg)]`. Establish `hPa : P * a ≠ 0` using `mul_ne_zero hP0 ha`. Establish `harg : (P * a).arg = P.arg + a.arg`.

Use `congrArg Complex.im (Complex.log_mul hP0 ha h1)` as an intermediate fact. Simplify `this` using `[Complex.log_im]`. Establish `h2 : (P * a).arg + b.arg ∈ Ioc (-Real.pi) Real.pi`. Rewrite using `[harg]`. Use `abs_add_le (P.arg + a.arg) b.arg` as an intermediate fact.

Use `abs_add_le P.arg a.arg` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Combine the linear relations using `[neg_abs_le (P.arg + a.arg + b.arg)]`. Combine the linear relations using `[le_abs_self (P.arg + a.arg + b.arg)]`. Rewrite using `[Complex.cpow_def_of_ne_zero (mul_ne_zero hPa hb), Complex.log_mul hPa hb h2, Complex.log_mul hP0 ha h1, Complex.cpow_def_of_ne_zero hP0, Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hb, ← Complex.exp_add, ← Complex.exp_add]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem cpow_split {P a b : ℂ} (hP : P ∈ Complex.slitPlane) (ha : a ≠ 0) (hb : b ≠ 0)
    (ha' : |a.arg| < (Real.pi - |P.arg|) / 2) (hb' : |b.arg| < (Real.pi - |P.arg|) / 2) (w : ℂ) :
    (P * a * b) ^ w = P ^ w * a ^ w * b ^ w := by
  have hP0 : P ≠ 0 := Complex.slitPlane_ne_zero hP
  have hPpi := abs_arg_lt_pi hP
  have hpos : 0 ≤ Real.pi - |P.arg| := by linarith
  have h1 : P.arg + a.arg ∈ Ioc (-Real.pi) Real.pi := by
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg)]
    · linarith [le_abs_self (P.arg + a.arg)]
  have hPa : P * a ≠ 0 := mul_ne_zero hP0 ha
  have harg : (P * a).arg = P.arg + a.arg := by
    have := congrArg Complex.im (Complex.log_mul hP0 ha h1)
    simpa [Complex.log_im] using this
  have h2 : (P * a).arg + b.arg ∈ Ioc (-Real.pi) Real.pi := by
    rw [harg]
    have := abs_add_le (P.arg + a.arg) b.arg
    have := abs_add_le P.arg a.arg
    constructor
    · linarith [neg_abs_le (P.arg + a.arg + b.arg)]
    · linarith [le_abs_self (P.arg + a.arg + b.arg)]
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hPa hb), Complex.log_mul hPa hb h2, Complex.log_mul hP0 ha h1,
    Complex.cpow_def_of_ne_zero hP0, Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hb,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/- English proof (translation)
Unfold `detD`. Rewrite using `[(h.iteratedFDeriv ℂ (Fintype.card ι)).eq_of_nhds]`.
-/
theorem detD_congr {ι : Type} [Fintype ι] [DecidableEq ι] {F G : Matrix ι ι ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) :
    detD F = detD G := by
  unfold detD
  rw [(h.iteratedFDeriv ℂ (Fintype.card ι)).eq_of_nhds]

/- English proof (translation)
Establish `hne : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0` using `hc.eventually_ne (by rw [h0]; exact one_ne_zero)`. Establish `hcont : ContinuousAt (fun T => (c T).arg) 0` using `ContinuousAt.comp (f := c) (g := Complex.arg) (Complex.continuousAt_arg (by rw [h0]; exact Complex.one_mem_slitPlane)) hc`. Establish `ht : Tendsto (fun T => (c T).arg) (𝓝 0) (𝓝 0)`. Use `hcont.tendsto` as an intermediate fact. Simplify `this` using `[h0, Complex.arg_one]`.

Use `filter_upwards [hne, ht (Metric.ball_mem_nhds 0 hδ)] with T h1 h2`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Simplify `h2` using `[Metric.mem_ball, Real.dist_eq]`.
-/
theorem ev_small {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {c : E → ℂ} (hc : ContinuousAt c 0) (h0 : c 0 = 1)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 ∧ |(c T).arg| < δ := by
  have hne : ∀ᶠ T in 𝓝 (0 : E), c T ≠ 0 := hc.eventually_ne (by rw [h0]; exact one_ne_zero)
  have hcont : ContinuousAt (fun T => (c T).arg) 0 :=
    ContinuousAt.comp (f := c) (g := Complex.arg) (Complex.continuousAt_arg (by rw [h0]; exact Complex.one_mem_slitPlane)) hc
  have ht : Tendsto (fun T => (c T).arg) (𝓝 0) (𝓝 0) := by
    have := hcont.tendsto
    simpa [h0, Complex.arg_one] using this
  filter_upwards [hne, ht (Metric.ball_mem_nhds 0 hδ)] with T h1 h2
  refine ⟨h1, ?_⟩
  simpa [Metric.mem_ball, Real.dist_eq] using h2

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]`.
-/
private theorem mul_toBlocks₂₁' (A B : M2 n) :
    (A * B).toBlocks₂₁ = A.toBlocks₂₁ * B.toBlocks₁₁ + A.toBlocks₂₂ * B.toBlocks₂₁ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]`.
-/
private theorem mul_toBlocks₂₂ (A B : M2 n) :
    (A * B).toBlocks₂₂ = A.toBlocks₂₁ * B.toBlocks₁₂ + A.toBlocks₂₂ * B.toBlocks₂₂ := by
  ext i j
  simp [Matrix.toBlocks₂₁, Matrix.toBlocks₁₂, Matrix.toBlocks₂₂, Matrix.mul_apply, Fintype.sum_sum_type]

/- English proof (translation)
Establish `hinv : (Cm n)⁻¹ = Cmi n` using `Matrix.inv_eq_left_inv cmi_mul_cm`. Establish `hxc21 : (x * Cm n).toBlocks₂₁ = u1 x`. Rewrite using `[mul_toBlocks₂₁', Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, u1]`. Simplify using `[Matrix.mul_smul]`. Establish `hxc22 : (x * Cm n).toBlocks₂₂ = u2 x`.

Rewrite using `[mul_toBlocks₂₂, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, u2]`. Simplify using `[Matrix.mul_smul]`. Rewrite using `[mX, hinv, show x * (Cm n * fromBlocks 1 Q R 1 * Cmi n) = (x * Cm n * fromBlocks 1 Q R 1) * Cmi n by`. Simplify using `only [Matrix.mul_assoc], first_cayley_block_mul_inverse_cayley, mul_toBlocks₂₁', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁,`. Use the proof step `Matrix.mul_one, hxc21, hxc22]`.
-/
private theorem u1_mul_mX_one_eq_add (x : M2 n) (Q R : Matrix (Fin n) (Fin n) ℂ) :
    u1 (x * mX 1 Q R 1) = u1 x + u2 x * R := by
  have hinv : (Cm n)⁻¹ = Cmi n := Matrix.inv_eq_left_inv cmi_mul_cm
  have hxc21 : (x * Cm n).toBlocks₂₁ = u1 x := by
    rw [mul_toBlocks₂₁', Cm, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁, u1]
    simp [Matrix.mul_smul]
  have hxc22 : (x * Cm n).toBlocks₂₂ = u2 x := by
    rw [mul_toBlocks₂₂, Cm, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂, u2]
    simp [Matrix.mul_smul]
  rw [mX, hinv, show x * (Cm n * fromBlocks 1 Q R 1 * Cmi n) = (x * Cm n * fromBlocks 1 Q R 1) * Cmi n by
    simp only [Matrix.mul_assoc], first_cayley_block_mul_inverse_cayley, mul_toBlocks₂₁', toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁,
    Matrix.mul_one, hxc21, hxc22]

/- English proof (translation)
Take `⟨hD, hP⟩` from `hx`. Establish `hD'` using `hD`. Take `⟨hdet, hu1, hu2, -⟩` from `hD'`. Take `⟨hQR, hRQ⟩` from `embOn_mul_embOn_compl j T S`. Establish `hdetM : (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1).det = x.det`.

Rewrite using `[Matrix.det_mul, det_mX_one _ _ hRQ, mul_one]`. Establish `hub : (ub1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det = (1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det`. Rewrite using `[inverse_first_block_mul_unipotent_domain x hD _ _ hQR hRQ, Matrix.det_mul, det_one_add_mul_comm, det_one_add_mul_embOn]`. Establish `hw : (wM x)⁻¹ = (u1 x)⁻¹ * u2 x`. Rewrite using `[wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu2)]`.

Establish `hu : (u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det = (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det`. Rewrite using `[u1_mul_mX_one_eq_add, ← det_one_add_mul_embOn, ← Matrix.det_mul]`. Use `congr 1`. Rewrite using `[hw, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu1), Matrix.one_mul]`. Unfold `fz`.

Rewrite using `[hdetM, hu, hub, show (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det * ((1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det) = (u1 x).det * (ub1 x).det * (1 + subOn (blkA j) (wM x) * T).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det by ring, cpow_split hP h2 h1 h2' h1' (-z), mul_z …`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fz_mX {m : ℕ} {e : ℤ} {z : ℂ} {j : ℕ} {x : M2 n} (hx : x ∈ DomZ n)
    (T : Matrix (blkA (n := n) j) (blkA j) ℂ) (S : Matrix (blkB (n := n) j) (blkB j) ℂ)
    (h1 : (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0) (h2 : (1 + subOn (blkA j) (wM x) * T).det ≠ 0)
    (h1' : |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2)
    (h2' : |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) :
    fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1) =
      (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
        (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z) := by
  obtain ⟨hD, hP⟩ := hx
  have hD' := hD
  obtain ⟨hdet, hu1, hu2, -⟩ := hD'
  obtain ⟨hQR, hRQ⟩ := embOn_mul_embOn_compl j T S
  have hdetM : (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1).det = x.det := by
    rw [Matrix.det_mul, det_mX_one _ _ hRQ, mul_one]
  have hub : (ub1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det := by
    rw [inverse_first_block_mul_unipotent_domain x hD _ _ hQR hRQ, Matrix.det_mul, det_one_add_mul_comm, det_one_add_mul_embOn]
  have hw : (wM x)⁻¹ = (u1 x)⁻¹ * u2 x := by
    rw [wM, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu2)]
  have hu : (u1 (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)).det =
      (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det := by
    rw [u1_mul_mX_one_eq_add, ← det_one_add_mul_embOn, ← Matrix.det_mul]
    congr 1
    rw [hw, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu1), Matrix.one_mul]
  unfold fz
  rw [hdetM, hu, hub,
    show (u1 x).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det * ((1 + subOn (blkA j) (wM x) * T).det * (ub1 x).det) =
      (u1 x).det * (ub1 x).det * (1 + subOn (blkA j) (wM x) * T).det * (1 + subOn (blkB j) (wM x)⁻¹ * S).det by ring,
    cpow_split hP h2 h1 h2' h1' (-z), mul_zpow, sub_eq_add_neg, Complex.cpow_add _ _ h1,
    show (-(m : ℂ)) = ((-(m : ℤ) : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]
  ring

/- English proof (translation)
Establish `hF : AnalyticAt ℂ (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) 0` using `analyticAt_det_one_add_cpow t`. Establish `h` using `CEq.equivar_thm ι (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) W hF`. Use `beta_reduce at h`. Rewrite using `[h]`. Use `congr 1`.

Establish `hG : AnalyticAt ℂ (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t) 0` using `analyticAt_det_one_add_cpow t`. Establish `hr` using `CEq.reindex_thm ι (Fin (Fintype.card ι)) (Fintype.equivFin ι) _ hG`. Use `beta_reduce at hr`. Rewrite using `[← kappaC (Fintype.card ι) t, ← hr]`. Use `congr 1`.

Use function extensionality and compare the values at `S`. Establish `hS : (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) + Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) S = Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (1 + S)`. Use extensionality with `a b`. Simplify using `[Matrix.reindex_apply, Matrix.one_apply]`. Rewrite using `[hS, Matrix.det_reindex_self]`.
-/
private theorem detD_det_one_add_mul_rpow_eq {ι : Type} [Fintype ι] [DecidableEq ι] (W : Matrix ι ι ℂ) (t : ℂ) :
    (detD fun S : Matrix ι ι ℂ => (1 + W * S).det ^ t) =
      W.det * ∏ i ∈ Finset.range (Fintype.card ι), (t + (i : ℂ)) := by
  have hF : AnalyticAt ℂ (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) 0 := analyticAt_det_one_add_cpow t
  have h := CEq.equivar_thm ι (fun S : Matrix ι ι ℂ => (1 + S).det ^ t) W hF
  beta_reduce at h
  rw [h]
  congr 1
  have hG : AnalyticAt ℂ (fun S : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ => (1 + S).det ^ t) 0 :=
    analyticAt_det_one_add_cpow t
  have hr := CEq.reindex_thm ι (Fin (Fintype.card ι)) (Fintype.equivFin ι) _ hG
  beta_reduce at hr
  rw [← kappaC (Fintype.card ι) t, ← hr]
  congr 1
  funext S
  have hS : (1 : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) ℂ) +
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) S =
      Matrix.reindex (Fintype.equivFin ι) (Fintype.equivFin ι) (1 + S) := by
    ext a b
    simp [Matrix.reindex_apply, Matrix.one_apply]
  rw [hS, Matrix.det_reindex_self]

/- English proof (translation)
Introduce `n m e j z x hj hx`. Establish `hx'` using `hx`. Take `⟨hD, hP⟩` from `hx'`. Establish `hδ : 0 < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2`. Use `abs_arg_lt_pi hP` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hcA : ∀ᶠ T in 𝓝 (0 : Matrix (blkA (n` using `n) j) (blkA j) ℂ), (1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧ |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 := ev_small (c := fun T => (1 + subOn (blkA j) (wM x) * T).det) ((continuous_const.add (continuous_const.matrix_mul continuo …`. Establish `hcB : ∀ᶠ S in 𝓝 (0 : Matrix (blkB (n` using `n) j) (blkB j) ℂ), (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0 ∧ |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 := ev_small (c := fun S => (1 + subOn (blkB j) (wM x)⁻¹ * S).det) ((continuous_const.add (continuous_const.matrix_mul co …`. Establish `hinner : ∀ T : Matrix (blkA (n` using `n) j) (blkA j) ℂ, ((1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧ |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) → (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ => fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) = (fz m …`. Introduce `T hT`.

Rewrite using `[PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun S : Matrix (blkB (n := n) j) (blkB j) ℂ => (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) * (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z)) ?_, detD_const_mul, detD_det_one_add_mul_rpow_eq]`. Use `filter_upwards [hcB] with S hS`. Conclude with `fz_mX hx T S hS.1 hT.1 hS.2 hT.2`. Rewrite using `[PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun T : Matrix (blkA (n := n) j) (blkA j) ℂ => (fz m e z x * ((subOn (blkB j) (wM x)⁻¹).det * ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ)))) * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) ?_]`. Rewrite using `[detD_const_mul, detD_det_one_add_mul_rpow_eq, card_blkA hj, card_blkB hj, minorOn_eq, minorOn_eq]`.

Establish `e1 : ∏ i ∈ Finset.range j, (-z + (i : ℂ)) = ∏ i ∈ Finset.range j, ((i : ℂ) - z)` using `Finset.prod_congr rfl (fun i _ => by ring)`. Establish `e2 : ∏ i ∈ Finset.range (n - j), ((-(m : ℂ)) - z + (i : ℂ)) = ∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z)` using `Finset.prod_congr rfl (fun i _ => by ring)`. Rewrite using `[e1, e2]`. Expand and normalize the polynomial expressions, which then agree. Use `filter_upwards [hcA] with T hT`.

Rewrite using `[hinner T hT]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem djZ : DjZ := by
  intro n m e j z x hj hx
  have hx' := hx
  obtain ⟨hD, hP⟩ := hx'
  have hδ : 0 < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 := by
    have := abs_arg_lt_pi hP
    linarith
  have hcA : ∀ᶠ T in 𝓝 (0 : Matrix (blkA (n := n) j) (blkA j) ℂ),
      (1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun T => (1 + subOn (blkA j) (wM x) * T).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hcB : ∀ᶠ S in 𝓝 (0 : Matrix (blkB (n := n) j) (blkB j) ℂ),
      (1 + subOn (blkB j) (wM x)⁻¹ * S).det ≠ 0 ∧
        |((1 + subOn (blkB j) (wM x)⁻¹ * S).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2 :=
    ev_small (c := fun S => (1 + subOn (blkB j) (wM x)⁻¹ * S).det)
      ((continuous_const.add (continuous_const.matrix_mul continuous_id)).matrix_det.continuousAt)
      (by simp) hδ
  have hinner : ∀ T : Matrix (blkA (n := n) j) (blkA j) ℂ,
      ((1 + subOn (blkA j) (wM x) * T).det ≠ 0 ∧
        |((1 + subOn (blkA j) (wM x) * T).det).arg| < (Real.pi - |((u1 x).det * (ub1 x).det).arg|) / 2) →
      (detD fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
          fz m e z (x * mX 1 (embOn (blkA j) T) (embOn (blkB j) S) 1)) =
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          ((subOn (blkB j) (wM x)⁻¹).det *
            ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ))) := by
    intro T hT
    rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun S : Matrix (blkB (n := n) j) (blkB j) ℂ =>
        (fz m e z x * (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) *
          (1 + subOn (blkB j) (wM x)⁻¹ * S).det ^ ((-(m : ℂ)) - z)) ?_,
      detD_const_mul, detD_det_one_add_mul_rpow_eq]
    filter_upwards [hcB] with S hS
    exact fz_mX hx T S hS.1 hT.1 hS.2 hT.2
  rw [PositivityTheory.Rg.Sw.HSt.detD_congr (G := fun T : Matrix (blkA (n := n) j) (blkA j) ℂ =>
      (fz m e z x * ((subOn (blkB j) (wM x)⁻¹).det *
        ∏ i ∈ Finset.range (Fintype.card (blkB (n := n) j)), ((-(m : ℂ)) - z + (i : ℂ)))) *
        (1 + subOn (blkA j) (wM x) * T).det ^ (-z)) ?_]
  · rw [detD_const_mul, detD_det_one_add_mul_rpow_eq, card_blkA hj, card_blkB hj, minorOn_eq, minorOn_eq]
    have e1 : ∏ i ∈ Finset.range j, (-z + (i : ℂ)) = ∏ i ∈ Finset.range j, ((i : ℂ) - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    have e2 : ∏ i ∈ Finset.range (n - j), ((-(m : ℂ)) - z + (i : ℂ)) =
        ∏ i ∈ Finset.range (n - j), ((i : ℂ) - m - z) :=
      Finset.prod_congr rfl (fun i _ => by ring)
    rw [e1, e2]
    ring
  · filter_upwards [hcA] with T hT
    rw [hinner T hT]
    ring

end PositivityTheory.Rg.Sw.HSt
