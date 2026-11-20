import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.IsMultZero
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter
open PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC PositivityTheory.Rg.BcB.CG
open PositivityTheory.RgTw (Mat G)
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.F.F0

/- English proof (translation)
Set `R : Matrix (Fin n) (Fin n) ℝ` to `Matrix.of fun a b => if a = b then (l a).re else if a < b then -1 else 0`. Establish `h : Formalism.REAL.Amat l = Complex.ofRealHom.mapMatrix R`. Use extensionality with `a b`. Simplify using `only [Formalism.REAL.Amat, RingHom.mapMatrix_apply, Matrix.map_apply, R, Matrix.of_apply]`. Use `split_ifs`.

Conclude with `Complex.ext (by simp) (by simp [hl])`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[h, ← map_pow]`. Simplify using `[RingHom.mapMatrix_apply]`.
-/
private lemma amat_pow_im {n : ℕ} (l : Fin n → ℂ) (hl : ∀ c, (l c).im = 0) (k : ℕ) (a b : Fin n) :
    ((Formalism.REAL.Amat l ^ k) a b).im = 0 := by
  let R : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun a b => if a = b then (l a).re else if a < b then -1 else 0
  have h : Formalism.REAL.Amat l = Complex.ofRealHom.mapMatrix R := by
    ext a b
    simp only [Formalism.REAL.Amat, RingHom.mapMatrix_apply, Matrix.map_apply, R, Matrix.of_apply]
    split_ifs
    · exact Complex.ext (by simp) (by simp [hl])
    · simp
    · simp
  rw [h, ← map_pow]
  simp [RingHom.mapMatrix_apply]

/- English proof (translation)
Establish `key : ∀ s : Bool, (GlobalTheory.Dec.gelfVal (infOf lam s) 2).im = 0`. Introduce `s`. Unfold `GlobalTheory.Dec.gelfVal`. Rewrite using `[Complex.im_sum]`. Use `Finset.sum_eq_zero fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Complex.im_sum]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Apply `amat_pow_im` to reduce the goal to its premises. Introduce `c`. Apply the tactic sequence `cases s <;> simp [infOf]`.

Simplify using `[cas, Complex.mul_im, key]`.
-/
theorem cas_infOf_im {n : ℕ} (lam : Fin n → ℤ) : (cas (infOf lam)).im = 0 := by
  have key : ∀ s : Bool, (GlobalTheory.Dec.gelfVal (infOf lam s) 2).im = 0 := by
    intro s
    unfold GlobalTheory.Dec.gelfVal
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_eq_zero fun b _ => ?_
    apply amat_pow_im
    intro c
    cases s <;> simp [infOf]
  simp [cas, Complex.mul_im, key]

/- English proof (translation)
Break down `mul_eq_zero.1 hs with h0 | h0` into its components or cases. Use `⟨fun t => Real.cos (t * s.im), by fun_prop, fun t => ?_, fun t ht => ?_⟩` and prove the remaining obligations. Establish `e : (t : ℂ) * s = ((t * s.im : ℝ) : ℂ) * Complex.I`. Apply the tactic sequence `apply Complex.ext <;> simp [h0]`. Rewrite using `[e, Complex.cosh_mul_I, Complex.ofReal_cos]`.

Establish `hr0 : 0 ≤ r` using `(lt_of_le_of_lt (abs_nonneg t) ht).le`. Establish `h1 : |t * s.im| < Real.pi / 2`. Rewrite using `[abs_mul]`. Establish `h2` using `Complex.abs_im_le_norm s`. Establish `hpi` using `Real.pi_gt_three`.

Establish `h3 : |t| * |s.im| ≤ r * ‖s‖` using `mul_le_mul ht.le h2 (abs_nonneg _) hr0`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `Real.cos_pos_of_mem_Ioo ⟨(abs_lt.1 h1).1, (abs_lt.1 h1).2⟩`. Use `⟨fun t => Real.cosh (t * s.re), by fun_prop, fun t => ?_, fun t _ => Real.cosh_pos _⟩` and prove the remaining obligations. Establish `e : (t : ℂ) * s = ((t * s.re : ℝ) : ℂ)`.

Apply the tactic sequence `apply Complex.ext <;> simp [h0]`. Rewrite using `[e, Complex.ofReal_cosh]`.
-/
private lemma cosh_real (s : ℂ) (r : ℝ) (hs : s.re * s.im = 0) (hrs : r * ‖s‖ < 1) :
    ∃ h : ℝ → ℝ, Continuous h ∧ (∀ t : ℝ, Complex.cosh ((t : ℂ) * s) = h t) ∧ ∀ t : ℝ, |t| < r → 0 < h t := by
  rcases mul_eq_zero.1 hs with h0 | h0
  · refine ⟨fun t => Real.cos (t * s.im), by fun_prop, fun t => ?_, fun t ht => ?_⟩
    · have e : (t : ℂ) * s = ((t * s.im : ℝ) : ℂ) * Complex.I := by
        apply Complex.ext <;> simp [h0]
      rw [e, Complex.cosh_mul_I, Complex.ofReal_cos]
    · have hr0 : 0 ≤ r := (lt_of_le_of_lt (abs_nonneg t) ht).le
      have h1 : |t * s.im| < Real.pi / 2 := by
        rw [abs_mul]
        have h2 := Complex.abs_im_le_norm s
        have hpi := Real.pi_gt_three
        have h3 : |t| * |s.im| ≤ r * ‖s‖ := mul_le_mul ht.le h2 (abs_nonneg _) hr0
        linarith
      exact Real.cos_pos_of_mem_Ioo ⟨(abs_lt.1 h1).1, (abs_lt.1 h1).2⟩
  · refine ⟨fun t => Real.cosh (t * s.re), by fun_prop, fun t => ?_, fun t _ => Real.cosh_pos _⟩
    have e : (t : ℂ) * s = ((t * s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [h0]
    rw [e, Complex.ofReal_cosh]

/- English proof (translation)
Establish `hs2 : (c ^ (1 / 2 : ℂ)) ^ 2 = c`. Rewrite using `[one_div]`. Conclude with `Complex.cpow_nat_inv_pow c two_ne_zero` after adjusting the coercions. Establish `hs : (c ^ (1 / 2 : ℂ)).re * (c ^ (1 / 2 : ℂ)).im = 0`. Establish `e : ((c ^ (1 / 2 : ℂ)) ^ 2).im = 2 * (c ^ (1 / 2 : ℂ)).re * (c ^ (1 / 2 : ℂ)).im`.

Simplify using `[pow_two, Complex.mul_im]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `e` using `[hs2, hc]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨h, hcont, heq, hpos⟩` from `cosh_real _ φ.rOut hs hrs`.

Establish `hnn : ∀ t, 0 ≤ φ t * h t`. Introduce `t`. Distinguish the cases in `ht : |t| < φ.rOut`. Conclude with `mul_nonneg φ.nonneg (hpos t ht).le`. Rewrite using `[φ.zero_of_le_dist (by simpa [Real.dist_eq] using not_lt.1 ht), zero_mul]`.

Use `⟨∫ t, φ t * h t, ?_, ?_⟩` and prove the remaining obligations. Use `Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) (φ.continuous.mul hcont) φ.hasCompactSupport.mul_right (fun t => hnn t) ?_` and prove the remaining obligations. Rewrite using `[φ.one_of_mem_closedBall (by simp [φ.rIn_pos.le]), one_mul]`. Conclude with `(hpos 0 (by simp [φ.rOut_pos])).ne'`. Simplify using `only [coshT]`.

Rewrite using `[← integral_complex_ofReal]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[heq t]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma coshT_bump (c : ℂ) (hc : c.im = 0) (φ : ContDiffBump (0 : ℝ)) (hrs : φ.rOut * ‖c ^ (1 / 2 : ℂ)‖ < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ coshT (fun t => φ t) c = ρ := by
  have hs2 : (c ^ (1 / 2 : ℂ)) ^ 2 = c := by
    rw [one_div]
    exact_mod_cast Complex.cpow_nat_inv_pow c two_ne_zero
  have hs : (c ^ (1 / 2 : ℂ)).re * (c ^ (1 / 2 : ℂ)).im = 0 := by
    have e : ((c ^ (1 / 2 : ℂ)) ^ 2).im = 2 * (c ^ (1 / 2 : ℂ)).re * (c ^ (1 / 2 : ℂ)).im := by
      simp [pow_two, Complex.mul_im]; ring
    rw [hs2, hc] at e
    linarith
  obtain ⟨h, hcont, heq, hpos⟩ := cosh_real _ φ.rOut hs hrs
  have hnn : ∀ t, 0 ≤ φ t * h t := by
    intro t
    by_cases ht : |t| < φ.rOut
    · exact mul_nonneg φ.nonneg (hpos t ht).le
    · rw [φ.zero_of_le_dist (by simpa [Real.dist_eq] using not_lt.1 ht), zero_mul]
  refine ⟨∫ t, φ t * h t, ?_, ?_⟩
  · refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0)
      (φ.continuous.mul hcont) φ.hasCompactSupport.mul_right (fun t => hnn t) ?_
    rw [φ.one_of_mem_closedBall (by simp [φ.rIn_pos.le]), one_mul]
    exact (hpos 0 (by simp [φ.rOut_pos])).ne'
  · simp only [coshT]
    rw [← integral_complex_ofReal]
    congr 1
    funext t
    rw [heq t]
    push_cast
    ring

/- English proof (translation)
Establish `hM : 0 ≤ ∑ i, ‖c i ^ (1 / 2 : ℂ)‖` using `Finset.sum_nonneg fun i _ => norm_nonneg _`. Set `φ : ContDiffBump (0 : ℝ)` to `⟨1 / (2 * (∑ i, ‖c i ^ (1 / 2 : ℂ)‖ + 1)), 1 / (∑ i, ‖c i ^ (1 / 2 : ℂ)‖ + 1), by positivity, one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩`. Establish `hr : ∀ i, φ.rOut * ‖c i ^ (1 / 2 : ℂ)‖ < 1`. Introduce `i`. Establish `hle : ‖c i ^ (1 / 2 : ℂ)‖ ≤ ∑ i, ‖c i ^ (1 / 2 : ℂ)‖` using `Finset.single_le_sum (f := fun i => ‖c i ^ (1 / 2 : ℂ)‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)`.

Use `show 1 / (∑ i, ‖c i ^ (1 / 2 : ℂ)‖ + 1) * _ < 1`. Rewrite using `[div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `choose ρ hρ hρeq using fun i => coshT_bump (c i) (hc i) φ (hr i)`. Establish `hP : 0 < ∏ i, ρ i` using `Finset.prod_pos fun i _ => hρ i`.

Set `lam : ℝ` to `(∏ i, ρ i) ^ (-(1 / (Fintype.card ι : ℝ)))`. Use `⟨fun t => lam * φ t, 1 / (∑ i, ‖c i ^ (1 / 2 : ℂ)‖ + 1), by positivity, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Conclude with `contDiff_const.mul φ.contDiff`. Introduce `t show lam * φ (-t) = lam * φ t`. Rewrite using `[φ.neg]`.

Introduce `t ht show lam * φ t = 0`. Rewrite using `[φ.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht.le), mul_zero]`. Establish `hsc : ∀ i, coshT (fun t => lam * φ t) (c i) = ((lam * ρ i : ℝ) : ℂ)`. Introduce `i`. Establish `e` using `hρeq i`.

Simplify using `only [coshT] at e ⊢`. Use `push_cast`. Repeatedly rewrite using `[mul_assoc]`. Rewrite using `[integral_const_mul, e]`. Rewrite using `[Finset.prod_congr rfl fun i _ => hsc i, ← Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]`.

Break down `Nat.eq_zero_or_pos (Fintype.card ι) with hN | hN` into its components or cases. Establish `: IsEmpty ι` using `Fintype.card_eq_zero_iff.1 hN`. Simplify using the standard rewrite rules. Establish `e : lam ^ Fintype.card ι * ∏ i, ρ i = 1`. Rewrite using `[← Real.rpow_natCast, ← Real.rpow_mul hP.le, neg_mul, one_div, inv_mul_cancel₀ (by exact_mod_cast hN.ne'), Real.rpow_neg_one, inv_mul_cancel₀ hP.ne']`.

Rewrite using `[e, Complex.ofReal_one]`.
-/
theorem bump_one (ι : Type) [Fintype ι] (c : ι → ℂ) (hc : ∀ i, (c i).im = 0) :
    ∃ (g : ℝ → ℝ) (T : ℝ), 0 ≤ T ∧ IsBump g T ∧ ∏ i, coshT g (c i) = 1 := by
  have hM : 0 ≤ ∑ i, ‖c i ^ (1 / 2 : ℂ)‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  let φ : ContDiffBump (0 : ℝ) :=
    ⟨1 / (2 * (∑ i, ‖c i ^ (1 / 2 : ℂ)‖ + 1)), 1 / (∑ i, ‖c i ^ (1 / 2 : ℂ)‖ + 1), by positivity,
      one_div_lt_one_div_of_lt (by positivity) (by linarith)⟩
  have hr : ∀ i, φ.rOut * ‖c i ^ (1 / 2 : ℂ)‖ < 1 := by
    intro i
    have hle : ‖c i ^ (1 / 2 : ℂ)‖ ≤ ∑ i, ‖c i ^ (1 / 2 : ℂ)‖ :=
      Finset.single_le_sum (f := fun i => ‖c i ^ (1 / 2 : ℂ)‖) (fun j _ => norm_nonneg _) (Finset.mem_univ i)
    show 1 / (∑ i, ‖c i ^ (1 / 2 : ℂ)‖ + 1) * _ < 1
    rw [div_mul_eq_mul_div, one_mul, div_lt_one (by positivity)]
    linarith
  choose ρ hρ hρeq using fun i => coshT_bump (c i) (hc i) φ (hr i)
  have hP : 0 < ∏ i, ρ i := Finset.prod_pos fun i _ => hρ i
  let lam : ℝ := (∏ i, ρ i) ^ (-(1 / (Fintype.card ι : ℝ)))
  refine ⟨fun t => lam * φ t, 1 / (∑ i, ‖c i ^ (1 / 2 : ℂ)‖ + 1), by positivity, ⟨?_, ?_, ?_⟩, ?_⟩
  · exact contDiff_const.mul φ.contDiff
  · intro t
    show lam * φ (-t) = lam * φ t
    rw [φ.neg]
  · intro t ht
    show lam * φ t = 0
    rw [φ.zero_of_le_dist (by rw [Real.dist_eq, sub_zero]; exact ht.le), mul_zero]
  · have hsc : ∀ i, coshT (fun t => lam * φ t) (c i) = ((lam * ρ i : ℝ) : ℂ) := by
      intro i
      have e := hρeq i
      simp only [coshT] at e ⊢
      push_cast
      simp_rw [mul_assoc]
      rw [integral_const_mul, e]
    rw [Finset.prod_congr rfl fun i _ => hsc i, ← Complex.ofReal_prod, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ]
    rcases Nat.eq_zero_or_pos (Fintype.card ι) with hN | hN
    · have : IsEmpty ι := Fintype.card_eq_zero_iff.1 hN
      simp
    · have e : lam ^ Fintype.card ι * ∏ i, ρ i = 1 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hP.le, neg_mul, one_div,
          inv_mul_cancel₀ (by exact_mod_cast hN.ne'), Real.rpow_neg_one, inv_mul_cancel₀ hP.ne']
      rw [e, Complex.ofReal_one]

/- English proof (translation)
Take `⟨m, c, w, g, ks, hks, hk, -⟩` from `h`. Establish `hkc : ContinuousOn k (GLs n)` using `(continuousOn_finsetSum Finset.univ fun i _ => ((hks i).2.1.continuousOn).const_smul (c i)).congr fun y hy => hk y hy`. Set `L : (M.V →L[ℂ] M.V) →ₗ[ℂ] ℂ` to `(LinearMap.trace ℂ M.V).comp ((ContinuousLinearMap.coeLM ℂ).comp (LinearMap.mulRight ℂ Tθ))`. Establish `hLc : Continuous L` using `L.continuous_of_finiteDimensional`. Establish `hphi : phiOf M Tθ k = fun y : G n => L (k y.val)` using `rfl`.

Establish `hval : ∀ y : G n, (y : Mat n) ∈ GLs n` using `fun y => ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hphi]`. Conclude with `hLc.comp (hkc.comp_continuous Units.continuous_val hval)`. Use `choose R hR using fun i => (hks i).2.2.1`.

Set `f : G n → Mat n × Mat n` to `fun y => ((y : Mat n), ((y⁻¹ : G n) : Mat n))`. Establish `hemb : Topology.IsClosedEmbedding f`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `e : f = (Prod.map id MulOpposite.unop) ∘ Units.embedProduct (Mat n)` using `rfl`. Rewrite using `[e]`.

Conclude with `((Homeomorph.refl _).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp Units.isEmbedding_embedProduct`. Establish `e : Set.range f = {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1}`. Use extensionality with `p`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, rfl⟩`.

Conclude with `⟨y.mul_inv, y.inv_mul⟩`. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨⟨p.1, p.2, h1, h2⟩, rfl⟩`. Rewrite using `[e]`. Conclude with `(isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)`.

Establish `hterm : ∀ p : Mat n × Mat n, ∀ a b, ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤ ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)`. Introduce `p a b`. Use `le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)) (fun a _ => by positivity) (Finset.mem_univ a))` and prove the remaining obligations. Conclude with `Finset.single_le_sum (f := fun b => (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)) (fun b _ => by positivity) (Finset.mem_univ b)`. Set `R₀ : ℝ` to `∑ i, |R i|`.

Set `K : Set (Mat n × Mat n)` to `{p | 1 + ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ Real.exp R₀}`. Establish `hK : IsCompact K`. Establish `h1 : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n => Metric.closedBall (0 : ℂ) (Real.exp R₀ + 1) : Set (Mat n))` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Use `(h1.prod h1).of_isClosed_subset ?_ ?_` and prove the remaining obligations. Use `isClosed_le (continuous_const.add (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => ?_)) continuous_const` and prove the remaining obligations.

Conclude with `((continuous_fst.matrix_elem a b).norm.pow 2).add ((continuous_snd.matrix_elem a b).norm.pow 2)`. Introduce `p hp`. Establish `hp' : 1 + ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ Real.exp R₀` using `hp`. Apply the tactic sequence `refine ⟨fun a _ b _ => ?_, fun a _ b _ => ?_⟩ <;>`. Apply the tactic sequence `simp only [Metric.mem_closedBall, dist_zero_right] <;>`.

Use polynomial arithmetic with `[hterm p a b, norm_nonneg (p.1 a b), norm_nonneg (p.2 a b), sq_nonneg (‖p.1 a b‖ - 1), sq_nonneg (‖p.2 a b‖ - 1)]`. Use `HasCompactSupport.intro (hemb.isCompact_preimage hK) fun y hy => ?_` and prove the remaining obligations. Establish `hlg : R₀ < lg (y : Mat n)`. Unfold `lg`. Rewrite using `[Real.lt_log_iff_exp_lt (by positivity)]`.

Establish `hy' : ¬ (1 + ∑ a, ∑ b, (‖(y : Mat n) a b‖ ^ 2 + ‖((y⁻¹ : G n) : Mat n) a b‖ ^ 2) ≤ Real.exp R₀)` using `hy`. Rewrite `hy'` using `[Matrix.coe_units_inv]`. Conclude with `not_le.1 hy'`. Establish `hk0 : k (y : Mat n) = 0`. Rewrite using `[hk _ (hval y)]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Establish `hRi : R i ≤ R₀` using `(le_abs_self _).trans (Finset.single_le_sum (f := fun i => |R i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))`. Rewrite using `[hR i _ (hval y) (lt_of_le_of_lt hRi hlg), smul_zero]`. Rewrite using `[hphi]`. Simplify using `[hk0]`.
-/
theorem phiOf_cs {n : ℕ} [MeasurableSpace (G n)] (μ : Measure (G n)) (M : KMod n) (Tθ : M.V →L[ℂ] M.V)
    (k : Mat n → (M.V →L[ℂ] M.V)) (val : Inf n → ℂ) (T : ℝ) (h : IsMult μ M k val T) :
    Continuous (phiOf M Tθ k) ∧ HasCompactSupport (phiOf M Tθ k) := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  have hkc : ContinuousOn k (GLs n) :=
    (continuousOn_finsetSum Finset.univ fun i _ => ((hks i).2.1.continuousOn).const_smul (c i)).congr
      fun y hy => hk y hy
  let L : (M.V →L[ℂ] M.V) →ₗ[ℂ] ℂ :=
    (LinearMap.trace ℂ M.V).comp ((ContinuousLinearMap.coeLM ℂ).comp (LinearMap.mulRight ℂ Tθ))
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hphi : phiOf M Tθ k = fun y : G n => L (k y.val) := rfl
  have hval : ∀ y : G n, (y : Mat n) ∈ GLs n := fun y =>
    ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero
  refine ⟨?_, ?_⟩
  · rw [hphi]
    exact hLc.comp (hkc.comp_continuous Units.continuous_val hval)
  · choose R hR using fun i => (hks i).2.2.1
    let f : G n → Mat n × Mat n := fun y => ((y : Mat n), ((y⁻¹ : G n) : Mat n))
    have hemb : Topology.IsClosedEmbedding f := by
      refine ⟨?_, ?_⟩
      · have e : f = (Prod.map id MulOpposite.unop) ∘ Units.embedProduct (Mat n) := rfl
        rw [e]
        exact ((Homeomorph.refl _).prodCongr MulOpposite.opHomeomorph.symm).isEmbedding.comp
          Units.isEmbedding_embedProduct
      · have e : Set.range f = {p | p.1 * p.2 = 1 ∧ p.2 * p.1 = 1} := by
          ext p
          constructor
          · rintro ⟨y, rfl⟩
            exact ⟨y.mul_inv, y.inv_mul⟩
          · rintro ⟨h1, h2⟩
            exact ⟨⟨p.1, p.2, h1, h2⟩, rfl⟩
        rw [e]
        exact (isClosed_eq (continuous_fst.mul continuous_snd) continuous_const).inter
          (isClosed_eq (continuous_snd.mul continuous_fst) continuous_const)
    have hterm : ∀ p : Mat n × Mat n, ∀ a b, ‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2 ≤
        ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) := by
      intro p a b
      refine le_trans ?_ (Finset.single_le_sum (f := fun a => ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2))
        (fun a _ => by positivity) (Finset.mem_univ a))
      exact Finset.single_le_sum (f := fun b => (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2)) (fun b _ => by positivity)
        (Finset.mem_univ b)
    let R₀ : ℝ := ∑ i, |R i|
    let K : Set (Mat n × Mat n) := {p | 1 + ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ Real.exp R₀}
    have hK : IsCompact K := by
      have h1 : IsCompact (Set.univ.pi fun _ : Fin n => Set.univ.pi fun _ : Fin n =>
          Metric.closedBall (0 : ℂ) (Real.exp R₀ + 1) : Set (Mat n)) :=
        isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
      refine (h1.prod h1).of_isClosed_subset ?_ ?_
      · refine isClosed_le (continuous_const.add (continuous_finsetSum _ fun a _ =>
          continuous_finsetSum _ fun b _ => ?_)) continuous_const
        exact ((continuous_fst.matrix_elem a b).norm.pow 2).add ((continuous_snd.matrix_elem a b).norm.pow 2)
      · intro p hp
        have hp' : 1 + ∑ a, ∑ b, (‖p.1 a b‖ ^ 2 + ‖p.2 a b‖ ^ 2) ≤ Real.exp R₀ := hp
        refine ⟨fun a _ b _ => ?_, fun a _ b _ => ?_⟩ <;>
          simp only [Metric.mem_closedBall, dist_zero_right] <;>
          nlinarith [hterm p a b, norm_nonneg (p.1 a b), norm_nonneg (p.2 a b),
            sq_nonneg (‖p.1 a b‖ - 1), sq_nonneg (‖p.2 a b‖ - 1)]
    refine HasCompactSupport.intro (hemb.isCompact_preimage hK) fun y hy => ?_
    have hlg : R₀ < lg (y : Mat n) := by
      unfold lg
      rw [Real.lt_log_iff_exp_lt (by positivity)]
      have hy' : ¬ (1 + ∑ a, ∑ b, (‖(y : Mat n) a b‖ ^ 2 + ‖((y⁻¹ : G n) : Mat n) a b‖ ^ 2) ≤ Real.exp R₀) := hy
      rw [Matrix.coe_units_inv] at hy'
      exact not_le.1 hy'
    have hk0 : k (y : Mat n) = 0 := by
      rw [hk _ (hval y)]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hRi : R i ≤ R₀ := (le_abs_self _).trans
        (Finset.single_le_sum (f := fun i => |R i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
      rw [hR i _ (hval y) (lt_of_le_of_lt hRi hlg), smul_zero]
    rw [hphi]
    simp [hk0]

end PositivityTheory.Rg.BcB.F.F0

end
