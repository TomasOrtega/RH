import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.OfRealNormSqSumMul

namespace ReciprocityTheory.L2DbarEstimates

open Filter Topology

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun w => (φ (u w) : ℂ)) (Complex.ofRealCLM.comp (deriv φ (u y) • fderiv ℝ u y)) y` using `Complex.ofRealCLM.hasFDerivAt.comp y (hφ.hasDerivAt.comp_hasFDerivAt y hu.hasFDerivAt)`. Establish `h2 : HasFDerivAt (fun w => (u w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u y)) y` using `Complex.ofRealCLM.hasFDerivAt.comp y hu.hasFDerivAt`. Apply the tactic sequence `constructor <;>`. Apply the tactic sequence `simp only [wd, wdb, h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_mul] <;> ring`.
-/
private theorem wd_wdb_ofReal_comp_of_differentiableAt {n : ℕ} {φ : ℝ → ℝ} {u : V n → ℝ} {y : V n}
    (hφ : DifferentiableAt ℝ φ (u y)) (hu : DifferentiableAt ℝ u y) (j : Fin n) :
    wd n j (fun w => (φ (u w) : ℂ)) y = ((deriv φ (u y) : ℝ) : ℂ) * wd n j (fun w => (u w : ℂ)) y ∧
      wdb n j (fun w => (φ (u w) : ℂ)) y = ((deriv φ (u y) : ℝ) : ℂ) * wdb n j (fun w => (u w : ℂ)) y := by
  have h1 : HasFDerivAt (fun w => (φ (u w) : ℂ))
      (Complex.ofRealCLM.comp (deriv φ (u y) • fderiv ℝ u y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y (hφ.hasDerivAt.comp_hasFDerivAt y hu.hasFDerivAt)
  have h2 : HasFDerivAt (fun w => (u w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hu.hasFDerivAt
  constructor <;>
    simp only [wd, wdb, h1.fderiv, h2.fderiv, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.ofRealCLM_apply, Complex.ofReal_mul] <;> ring

/- English proof (translation)
Establish `h2 : HasFDerivAt (fun w => (u w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u y)) y` using `Complex.ofRealCLM.hasFDerivAt.comp y hu.hasFDerivAt`. Simplify using `only [wd, wdb, h2.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, map_div₀, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem wdb_ofReal_eq_conj_wd_ofReal {n : ℕ} {u : V n → ℝ} {y : V n} (hu : DifferentiableAt ℝ u y) (j : Fin n) :
    wdb n j (fun w => (u w : ℂ)) y = (starRingEnd ℂ) (wd n j (fun w => (u w : ℂ)) y) := by
  have h2 : HasFDerivAt (fun w => (u w : ℂ)) (Complex.ofRealCLM.comp (fderiv ℝ u y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hu.hasFDerivAt
  simp only [wd, wdb, h2.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, map_div₀,
    map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  ring

/- English proof (translation)
Establish `hF : fderiv ℝ (fun w => p w * q w) y = p y • fderiv ℝ q y + q y • fderiv ℝ p y` using `(hp.hasFDerivAt.mul hq.hasFDerivAt).fderiv`. Simplify using `only [wd, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem wd_mul_apply {n : ℕ} {p q : V n → ℂ} {y : V n} (hp : DifferentiableAt ℝ p y)
    (hq : DifferentiableAt ℝ q y) (j : Fin n) :
    wd n j (fun w => p w * q w) y = wd n j p y * q y + p y * wd n j q y := by
  have hF : fderiv ℝ (fun w => p w * q w) y = p y • fderiv ℝ q y + q y • fderiv ℝ p y :=
    (hp.hasFDerivAt.mul hq.hasFDerivAt).fderiv
  simp only [wd, hF, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/- English proof (translation)
Establish `h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y` using `hg.fderiv_right (by norm_num)`. Establish `hb : ∀ u : V n, DifferentiableAt ℝ (fun v => fderiv ℝ g v u) y` using `fun u => (h1.clm_apply contDiffAt_const).differentiableAt one_ne_zero`. Use `((hb (bas n k)).add ((hb (Complex.I • bas n k)).const_mul Complex.I)).mul_const (2⁻¹ : ℂ)` as an intermediate fact. Unfold `wdb`. Simplify using `only [div_eq_mul_inv]`.

Conclude with `this`.
-/
private theorem differentiableAt_wdb_of_contDiffAt_two {n : ℕ} {g : V n → ℂ} {y : V n} (hg : ContDiffAt ℝ 2 g y) (k : Fin n) :
    DifferentiableAt ℝ (wdb n k g) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ g) y := hg.fderiv_right (by norm_num)
  have hb : ∀ u : V n, DifferentiableAt ℝ (fun v => fderiv ℝ g v u) y := fun u =>
    (h1.clm_apply contDiffAt_const).differentiableAt one_ne_zero
  have := ((hb (bas n k)).add ((hb (Complex.I • bas n k)).const_mul Complex.I)).mul_const (2⁻¹ : ℂ)
  unfold wdb
  simp only [div_eq_mul_inv]
  exact this

/- English proof (translation)
Introduce `z hz φ v hφ hv x ξ`. Take `⟨e, he, hx⟩` from `exists_chart n z hz x`. Establish `hT : e.target ∈ 𝓝 (z x)`. Rewrite using `[he hx]`. Conclude with `e.open_target.mem_nhds (e.map_source hx)`.

Establish `hx' : e.symm (z x) = x` using `by rw [he hx, e.left_inv hx]`. Establish `hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ((v (e.symm y) : ℝ) : ℂ)) e.target` using `hv e he`. Establish `hur : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => v (e.symm y)) e.target`. Use `Complex.reCLM.contDiff.comp_contDiffOn hU` as an intermediate fact. Conclude with `this.congr fun y _ => by simp`.

Establish `hu2 : ∀ y ∈ e.target, ContDiffAt ℝ 2 (fun y => v (e.symm y)) y` using `fun y hy => (contDiffOn_infty.1 hur 2).contDiffAt (e.open_target.mem_nhds hy)`. Establish `hud : ∀ y ∈ e.target, DifferentiableAt ℝ (fun y => v (e.symm y)) y` using `fun y hy => (hu2 y hy).differentiableAt (by simp)`. Establish `hz0 : z x ∈ e.target` using `mem_of_mem_nhds hT`. Establish `hU2 : ContDiffAt ℝ 2 (fun y => ((v (e.symm y) : ℝ) : ℂ)) (z x)` using `(contDiffOn_infty.1 hU 2).contDiffAt hT`. Establish `hφ1 : ContDiff ℝ 1 (deriv φ)` using `((contDiff_succ_iff_deriv (n := 1)).1 (by rw [one_add_one_eq_two]; exact hφ)).2.2`.

Establish `hφd : ∀ t, DifferentiableAt ℝ φ t` using `fun t => hφ.differentiable (by simp) t`. Establish `hφ1d : ∀ t, DifferentiableAt ℝ (deriv φ) t` using `fun t => hφ1.differentiable one_ne_zero t`. Establish `ev : ∀ l, wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ)) =ᶠ[𝓝 (z x)] fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ) * wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) y`. Introduce `l`. Use `filter_upwards [hT] with y hy`.

Conclude with `(wd_wdb_ofReal_comp_of_differentiableAt (hφd _) (hud y hy) l).2`. Establish `key : ∀ j l, wd n j (wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ))) (z x) = ((deriv φ (v (e.symm (z x))) : ℝ) : ℂ) * wd n j (wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ))) (z x) + ((deriv (deriv φ) (v (e.symm (z x))) : ℝ) : ℂ) * (wd n j (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x) * …`. Introduce `j l`. Establish `e1 : wd n j (wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ))) (z x) = wd n j (fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ) * wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) y) (z x)`. Simplify using `only [wd, (ev l).fderiv_eq]`.

Establish `hp : DifferentiableAt ℝ (fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ)) (z x)` using `Complex.ofRealCLM.differentiableAt.comp (z x) ((hφ1d _).comp (z x) (hud _ hz0))`. Rewrite using `[e1, wd_mul_apply hp (differentiableAt_wdb_of_contDiffAt_two hU2 l) j, (wd_wdb_ofReal_comp_of_differentiableAt (hφ1d _) (hud _ hz0) j).1, ← wdb_ofReal_eq_conj_wd_ofReal (hud _ hz0) l]`. Apply the tactic sequence `try beta_reduce`. Expand and normalize the polynomial expressions, which then agree. Establish `hdd : dDot n z (fun y => (v y : ℂ)) x ξ = ∑ j, wd n j (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x) * ξ j`.

Unfold `dDot`. Conclude with `Finset.sum_congr rfl fun j _ => by rw [d_eq_wd n z e he j _ x hx]; rfl`. Rewrite using `[levi_eq_leviV n z e he _ x hx ξ, levi_eq_leviV n z e he v x hx ξ, hdd, Complex.sq_norm, ← Complex.mul_conj]`. Unfold `leviV`. Apply the tactic sequence `try beta_reduce`.

Simplify using `only [key, hx']`. Rewrite using `[map_sum]`. Simplify using `only [map_mul]`. Rewrite using `[Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chain (n : ℕ) (M : Type*) [TopologicalSpace M] : ChainStatement n M := by
  intro z hz φ v hφ hv x ξ
  obtain ⟨e, he, hx⟩ := exists_chart n z hz x
  have hT : e.target ∈ 𝓝 (z x) := by
    rw [he hx]; exact e.open_target.mem_nhds (e.map_source hx)
  have hx' : e.symm (z x) = x := by rw [he hx, e.left_inv hx]
  have hU : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ((v (e.symm y) : ℝ) : ℂ)) e.target := hv e he
  have hur : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => v (e.symm y)) e.target := by
    have := Complex.reCLM.contDiff.comp_contDiffOn hU
    exact this.congr fun y _ => by simp
  have hu2 : ∀ y ∈ e.target, ContDiffAt ℝ 2 (fun y => v (e.symm y)) y := fun y hy =>
    (contDiffOn_infty.1 hur 2).contDiffAt (e.open_target.mem_nhds hy)
  have hud : ∀ y ∈ e.target, DifferentiableAt ℝ (fun y => v (e.symm y)) y := fun y hy =>
    (hu2 y hy).differentiableAt (by simp)
  have hz0 : z x ∈ e.target := mem_of_mem_nhds hT
  have hU2 : ContDiffAt ℝ 2 (fun y => ((v (e.symm y) : ℝ) : ℂ)) (z x) :=
    (contDiffOn_infty.1 hU 2).contDiffAt hT
  have hφ1 : ContDiff ℝ 1 (deriv φ) :=
    ((contDiff_succ_iff_deriv (n := 1)).1 (by rw [one_add_one_eq_two]; exact hφ)).2.2
  have hφd : ∀ t, DifferentiableAt ℝ φ t := fun t => hφ.differentiable (by simp) t
  have hφ1d : ∀ t, DifferentiableAt ℝ (deriv φ) t := fun t => hφ1.differentiable one_ne_zero t
  have ev : ∀ l, wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ)) =ᶠ[𝓝 (z x)]
      fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ) * wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) y := by
    intro l
    filter_upwards [hT] with y hy
    exact (wd_wdb_ofReal_comp_of_differentiableAt (hφd _) (hud y hy) l).2
  have key : ∀ j l, wd n j (wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ))) (z x) =
      ((deriv φ (v (e.symm (z x))) : ℝ) : ℂ) * wd n j (wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ))) (z x) +
        ((deriv (deriv φ) (v (e.symm (z x))) : ℝ) : ℂ) *
          (wd n j (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x) *
            (starRingEnd ℂ) (wd n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x))) := by
    intro j l
    have e1 : wd n j (wdb n l (fun y => ((φ (v (e.symm y)) : ℝ) : ℂ))) (z x) =
        wd n j (fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ) *
          wdb n l (fun w => ((v (e.symm w) : ℝ) : ℂ)) y) (z x) := by
      simp only [wd, (ev l).fderiv_eq]
    have hp : DifferentiableAt ℝ (fun y => ((deriv φ (v (e.symm y)) : ℝ) : ℂ)) (z x) :=
      Complex.ofRealCLM.differentiableAt.comp (z x) ((hφ1d _).comp (z x) (hud _ hz0))
    rw [e1, wd_mul_apply hp (differentiableAt_wdb_of_contDiffAt_two hU2 l) j, (wd_wdb_ofReal_comp_of_differentiableAt (hφ1d _) (hud _ hz0) j).1, ← wdb_ofReal_eq_conj_wd_ofReal (hud _ hz0) l]
    try beta_reduce
    ring
  have hdd : dDot n z (fun y => (v y : ℂ)) x ξ =
      ∑ j, wd n j (fun w => ((v (e.symm w) : ℝ) : ℂ)) (z x) * ξ j := by
    unfold dDot
    exact Finset.sum_congr rfl fun j _ => by rw [d_eq_wd n z e he j _ x hx]; rfl
  rw [levi_eq_leviV n z e he _ x hx ξ, levi_eq_leviV n z e he v x hx ξ, hdd, Complex.sq_norm,
    ← Complex.mul_conj]
  unfold leviV
  try beta_reduce
  simp only [key, hx']
  rw [map_sum]
  simp only [map_mul]
  rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

end ReciprocityTheory.L2DbarEstimates
