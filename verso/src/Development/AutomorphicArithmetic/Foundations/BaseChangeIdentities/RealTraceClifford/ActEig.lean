import Mathlib
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.RealTrOfAll
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.EpowSmul
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.LgCpt
import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.RealTraceClifford.HderEntry

noncomputable section

open MeasureTheory Matrix Finset GlobalTheory.OpTrace GlobalTheory.AutomorphicL2Unitary
open scoped InnerProductSpace ComplexConjugate ContDiff
open PositivityTheory.RgTw (Mat G th IsThetaOp)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD UpperTheory.RealTr

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hl : HasDerivAt (fun s : ℝ => (s : ℂ) * a) a t`. Use `((hasDerivAt_id (t : ℂ)).mul_const a).comp_ofReal` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `this`. Establish `h2` using `((Complex.hasDerivAt_cosh ((t : ℂ) * a)).comp t hl).smul_const v`.

Rewrite using `[mul_comm a]`. Conclude with `h2`.
-/
private theorem hasDerivAt_cosh_smul' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (a : ℂ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v) ((a * Complex.sinh ((t : ℂ) * a)) • v) t := by
  have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * a) a t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const a).comp_ofReal
    rw [one_mul] at this
    exact this
  have h2 := ((Complex.hasDerivAt_cosh ((t : ℂ) * a)).comp t hl).smul_const v
  rw [mul_comm a]
  exact h2

/- English proof (translation)
Establish `hl : HasDerivAt (fun s : ℝ => (s : ℂ) * a) a t`. Use `((hasDerivAt_id (t : ℂ)).mul_const a).comp_ofReal` as an intermediate fact. Rewrite `this` using `[one_mul]`. Conclude with `this`. Establish `h2` using `((Complex.hasDerivAt_sinh ((t : ℂ) * a)).comp t hl).smul_const v`.

Rewrite using `[mul_comm a]`. Conclude with `h2`.
-/
private theorem hasDerivAt_sinh_smul' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (a : ℂ) (v : V) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.sinh ((s : ℂ) * a) • v) ((a * Complex.cosh ((t : ℂ) * a)) • v) t := by
  have hl : HasDerivAt (fun s : ℝ => (s : ℂ) * a) a t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const a).comp_ofReal
    rw [one_mul] at this
    exact this
  have h2 := ((Complex.hasDerivAt_sinh ((t : ℂ) * a)).comp t hl).smul_const v
  rw [mul_comm a]
  exact h2

/- English proof (translation)
Establish `hd : deriv (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v) = fun s : ℝ => a • (Complex.sinh ((s : ℂ) * a) • v)`. Use function extensionality and compare the values at `s`. Rewrite using `[(hasDerivAt_cosh_smul' a v s).deriv, mul_smul]`. Rewrite using `[iteratedDeriv_succ, iteratedDeriv_one, hd]`. Establish `h : HasDerivAt (fun s : ℝ => a • (Complex.sinh ((s : ℂ) * a) • v)) (a • ((a * Complex.cosh ((t : ℂ) * a)) • v)) t` using `(hasDerivAt_sinh_smul' a v t).const_smul a`.

Rewrite using `[h.deriv, smul_smul, mul_assoc]`.
-/
private theorem iteratedDeriv_two_cosh_smul' {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (a : ℂ) (v : V) (t : ℝ) :
    iteratedDeriv 2 (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v) t
      = (a * a * Complex.cosh ((t : ℂ) * a)) • v := by
  have hd : deriv (fun s : ℝ => Complex.cosh ((s : ℂ) * a) • v)
      = fun s : ℝ => a • (Complex.sinh ((s : ℂ) * a) • v) := by
    funext s
    rw [(hasDerivAt_cosh_smul' a v s).deriv, mul_smul]
  rw [iteratedDeriv_succ, iteratedDeriv_one, hd]
  have h : HasDerivAt (fun s : ℝ => a • (Complex.sinh ((s : ℂ) * a) • v))
      (a • ((a * Complex.cosh ((t : ℂ) * a)) • v)) t := (hasDerivAt_sinh_smul' a v t).const_smul a
  rw [h.deriv, smul_smul, mul_assoc]

/- English proof (translation)
Break down `eq_or_ne c 0 with rfl | hc` into its components or cases. Rewrite using `[Complex.zero_cpow (by norm_num)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← Complex.cpow_add _ _ hc]`. Evaluate the numerical expressions.
-/
private theorem half_mul_half' (c : ℂ) : c ^ (1 / 2 : ℂ) * c ^ (1 / 2 : ℂ) = c := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [Complex.zero_cpow (by norm_num)]
    ring
  · rw [← Complex.cpow_add _ _ hc]
    norm_num

/- English proof (translation)
Establish `h0 : ContDiff ℝ ∞ Complex.cosh` using `Complex.contDiff_cosh.restrict_scalars ℝ`. Establish `h1 : ContDiff ℝ ∞ (fun p : ℝ × Mat n => (p.1 : ℂ))` using `Complex.ofRealCLM.contDiff.comp contDiff_fst`. Conclude with `h0.comp (h1.mul contDiff_const)`.
-/
private theorem contDiff_cosh_fst {n : ℕ} (a : ℂ) :
    ContDiff ℝ ∞ (fun p : ℝ × Mat n => Complex.cosh ((p.1 : ℂ) * a)) := by
  have h0 : ContDiff ℝ ∞ Complex.cosh := Complex.contDiff_cosh.restrict_scalars ℝ
  have h1 : ContDiff ℝ ∞ (fun p : ℝ × Mat n => (p.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  exact h0.comp (h1.mul contDiff_const)

/- English proof (translation)
Establish `ha2` using `half_mul_half' (cas χ)`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h2 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => f p.2) (Set.univ ×ˢ GLs n)` using `hf.1.comp contDiff_snd.contDiffOn (fun p hp => hp.2)`. Conclude with `(contDiff_cosh_fst _).contDiffOn.smul h2`. Introduce `t`.

Use `⟨contDiffOn_const.smul hf.1, ?_⟩` and prove the remaining obligations. Introduce `g hg k`. Simplify using `only [hf.2 g hg k, map_smul]`. Introduce `t g hg`. Establish `h` using `((UpperTheory.RealTr.zEig n E.V χ f hf.1 he (Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)))).1 g hg)`.

Use `beta_reduce`. Rewrite using `[iteratedDeriv_two_cosh_smul', h, ha2, smul_smul]`. Introduce `g hg beta_reduce`. Rewrite using `[(hasDerivAt_cosh_smul' _ (f g) 0).deriv]`. Simplify using the standard rewrite rules.
-/
private theorem eigWave {n : ℕ} (E : KMod n) (χ : Inf n) (f : Mat n → E.V) (hf : f ∈ CE E) (he : IsEig χ f) :
    IsWave E (fun (t : ℝ) y => Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f y) := by
  have ha2 := half_mul_half' (cas χ)
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => f p.2) (Set.univ ×ˢ GLs n) :=
      hf.1.comp contDiff_snd.contDiffOn (fun p hp => hp.2)
    exact (contDiff_cosh_fst _).contDiffOn.smul h2
  · intro t
    refine ⟨contDiffOn_const.smul hf.1, ?_⟩
    intro g hg k
    simp only [hf.2 g hg k, map_smul]
  · intro t g hg
    have h := ((UpperTheory.RealTr.zEig n E.V χ f hf.1 he (Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)))).1 g hg)
    beta_reduce
    rw [iteratedDeriv_two_cosh_smul', h, ha2, smul_smul]
  · intro g hg
    beta_reduce
    rw [(hasDerivAt_cosh_smul' _ (f g) 0).deriv]
    simp

/- English proof (translation)
Conclude with `((UpperTheory.RealTr.basic n).2.1 _).2 y.isUnit`.
-/
private theorem val_mem_GLs' {n : ℕ} (y : G n) : y.val ∈ GLs n := by
  exact ((UpperTheory.RealTr.basic n).2.1 _).2 y.isUnit

/- English proof (translation)
Take `⟨R, hR⟩` from `hs`. Establish `hcont : Continuous (fun y : G n => κ y.val (f (x * y.val)))`. Use `Continuous.clm_apply (hc.comp_continuous Units.continuous_val fun y => val_mem_GLs' y) ?_` and prove the remaining obligations. Use `hf.comp_continuous (continuous_const.mul Units.continuous_val) fun y => ?_` and prove the remaining obligations. Use `show det (x * y.val) ≠ 0`.

Rewrite using `[det_mul]`. Conclude with `mul_ne_zero hx (val_mem_GLs' y)`. Use `hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (UpperTheory.RealTr.lgCpt n R) ?_)` and prove the remaining obligations. Introduce `y hy`. Simplify using `only [Set.mem_setOf_eq, not_le] at hy`.

Simplify using `[hR _ (val_mem_GLs' y) hy]`.
-/
private theorem integrable_ker {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (κ : Mat n → (E.V →L[ℂ] E.V)) (hc : ContinuousOn κ (GLs n))
    (hs : ∃ R, ∀ y ∈ GLs n, R < lg y → κ y = 0) (f : Mat n → E.V) (hf : ContinuousOn f (GLs n))
    (x : Mat n) (hx : x ∈ GLs n) : Integrable (fun y : G n => κ y.val (f (x * y.val))) μ := by
  obtain ⟨R, hR⟩ := hs
  have hcont : Continuous (fun y : G n => κ y.val (f (x * y.val))) := by
    refine Continuous.clm_apply (hc.comp_continuous Units.continuous_val fun y => val_mem_GLs' y) ?_
    refine hf.comp_continuous (continuous_const.mul Units.continuous_val) fun y => ?_
    show det (x * y.val) ≠ 0
    rw [det_mul]
    exact mul_ne_zero hx (val_mem_GLs' y)
  refine hcont.integrable_of_hasCompactSupport (HasCompactSupport.intro (UpperTheory.RealTr.lgCpt n R) ?_)
  intro y hy
  simp only [Set.mem_setOf_eq, not_le] at hy
  simp [hR _ (val_mem_GLs' y) hy]

/- English proof (translation)
Introduce `n _ _ μ _ E k val T hM χ f hf he x hx`. Take `⟨m, c, w, g, ks, hks, hk, hval⟩` from `hM`. Establish `hf'` using `hf`. Take `⟨hf1, hf2⟩` from `hf'`. Establish `hint : ∀ i, Integrable (fun y : G n => ks i y.val (f (x * y.val))) μ` using `fun i => integrable_ker μ E (ks i) (hks i).2.1.continuousOn (hks i).2.2.1 f hf1.continuousOn x hx`.

Establish `hu` using `eigWave E χ f hf he`. Establish `hact : ∀ i, act μ E (ks i) f x = (coshT (g i) (cas χ) * zVal (w i) χ) • f x`. Introduce `i`. Establish `key` using `(hks i).2.2.2.2 _ hu x hx`. Establish `e1 : act μ E (ks i) f x = act μ E (ks i) (fun y => Complex.cosh (((0 : ℝ) : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f y) x`.

Simplify using the standard rewrite rules. Establish `e2 : (fun x' => ∫ t : ℝ, ((g i t : ℝ) : ℂ) • (Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f x')) = fun x' => coshT (g i) (cas χ) • f x'`. Use function extensionality and compare the values at `x'`. Simplify using `only [smul_smul]`. Rewrite using `[integral_smul_const]`.

Both sides reduce to the same expression. Rewrite using `[e1]`. Use `key.trans ((congrArg (fun F => zOp (w i) F x) e2).trans ?_)` and prove the remaining obligations. Conclude with `(UpperTheory.RealTr.zEig n E.V χ f hf1 he _).2 (w i) x hx`. Establish `hk' : ∀ y : G n, k y.val = ∑ i, c i • ks i y.val` using `fun y => hk _ (val_mem_GLs' y)`.

Establish `hsum : act μ E k f x = ∑ i, c i • act μ E (ks i) f x`. Simplify using `only [act, hk', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]`. Rewrite using `[integral_finset_sum]`. Simplify using `only [integral_smul]`. Introduce `i _`.

Conclude with `(hint i).smul (c i)`. Rewrite using `[hsum, hval]`. Simplify using `only [hact, smul_smul, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.RealTr.actEig :
    ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T →
      ∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x := by
  intro n _ _ μ _ E k val T hM χ f hf he x hx
  obtain ⟨m, c, w, g, ks, hks, hk, hval⟩ := hM
  have hf' := hf
  obtain ⟨hf1, hf2⟩ := hf'
  have hint : ∀ i, Integrable (fun y : G n => ks i y.val (f (x * y.val))) μ := fun i =>
    integrable_ker μ E (ks i) (hks i).2.1.continuousOn (hks i).2.2.1 f hf1.continuousOn x hx
  have hu := eigWave E χ f hf he
  have hact : ∀ i, act μ E (ks i) f x = (coshT (g i) (cas χ) * zVal (w i) χ) • f x := by
    intro i
    have key := (hks i).2.2.2.2 _ hu x hx
    have e1 : act μ E (ks i) f x =
        act μ E (ks i) (fun y => Complex.cosh (((0 : ℝ) : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f y) x := by
      simp
    have e2 : (fun x' => ∫ t : ℝ, ((g i t : ℝ) : ℂ) • (Complex.cosh ((t : ℂ) * cas χ ^ (1 / 2 : ℂ)) • f x')) =
        fun x' => coshT (g i) (cas χ) • f x' := by
      funext x'
      simp only [smul_smul]
      rw [integral_smul_const]
      rfl
    rw [e1]
    refine key.trans ((congrArg (fun F => zOp (w i) F x) e2).trans ?_)
    exact (UpperTheory.RealTr.zEig n E.V χ f hf1 he _).2 (w i) x hx
  have hk' : ∀ y : G n, k y.val = ∑ i, c i • ks i y.val := fun y => hk _ (val_mem_GLs' y)
  have hsum : act μ E k f x = ∑ i, c i • act μ E (ks i) f x := by
    simp only [act, hk', ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
    rw [integral_finset_sum]
    · simp only [integral_smul]
    · intro i _
      exact (hint i).smul (c i)
  rw [hsum, hval]
  simp only [hact, smul_smul, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  ring
