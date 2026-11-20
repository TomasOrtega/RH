import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoWeightStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.BigCellPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hall : ∀ k, ∀ x ∈ X.dom, Fl.s k x = 0` using `fun k => bigCell_of lu_holds r X x0 hx0 Xa.L (Fl.s k) ⟨(Fl.s_van k).1.1.1.1, (Fl.s_van k).1.1.1.2.1⟩ (hcon k)`. Establish `hx0d` using `IW.orth_mem_dom X x0 hx0`. Take `⟨j, -⟩` from `(Fl.S_eq x0 hx0d).1 (fun k => hall k x0 hx0d)`.

Establish `hc` using `Fl.coord j`. Establish `h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j)` using `by show cpt X (Fl.xs j) 0 ∈ X.dom`. Rewrite using `[IW.cpt_zero]`. Conclude with `Fl.xs_mem j`. Establish `hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k => Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0` using `by filter_upwards [(ExF.isOpen_OmF X _).mem_nhds h0] with z hz`.

Simplify using `[hall _ _ hz]`. Both sides reduce to the same expression. Rewrite `hc` using `[hev.fderiv_eq, fderiv_const_apply]`. Apply `hc` to reduce the goal to its premises. Establish `h2` using `Xa.n_ge`.

Rewrite using `[ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero]`. Simplify using `only [finrank_euclideanSpace, Fintype.card_fin]`. Conclude with `zero_pow (by omega)`.
-/
theorem exists_s_ne {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (hx0 : IsOrth X x0) :
    ∃ k0 : Fin (nd X), ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  have hall : ∀ k, ∀ x ∈ X.dom, Fl.s k x = 0 := fun k =>
    bigCell_of lu_holds r X x0 hx0 Xa.L (Fl.s k) ⟨(Fl.s_van k).1.1.1.1, (Fl.s_van k).1.1.1.2.1⟩ (hcon k)
  have hx0d := IW.orth_mem_dom X x0 hx0
  obtain ⟨j, -⟩ := (Fl.S_eq x0 hx0d).1 (fun k => hall k x0 hx0d)
  have hc := Fl.coord j
  have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
    show cpt X (Fl.xs j) 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact Fl.xs_mem j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(ExF.isOpen_OmF X _).mem_nhds h0] with z hz
    simp [hall _ _ hz]
    rfl
  rw [hev.fderiv_eq, fderiv_const_apply] at hc
  apply hc
  have h2 := Xa.n_ge
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  exact zero_pow (by omega)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def Gf (Xa : ArchInM X) (Fl : FlatM X Xa) (g : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : ℝ≥0∞ :=
  ENNReal.ofReal (‖g x‖ ^ 2) * WSk X Xa Fl x

/- English proof (translation)
Establish `hm` using `(IW.isOpen_dom X).measurableSet`. Establish `h1 : Measurable (X.dom.piecewise g 0)` using `hg.measurable_piecewise continuousOn_const hm`. Establish `h2` using `((h1.norm.pow_const 2).ennreal_ofReal).mul (WSk_meas Xa Fl)`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`.

Distinguish the cases in `hx : x ∈ X.dom`. Simplify using `[Gf, hx]`. Simplify using `[Gf, WSk, hx]`.
-/
theorem Gf_meas (Xa : ArchInM X) (Fl : FlatM X Xa) {g : Frame X.Ψ r → ℂ} (hg : ContinuousOn g X.dom) :
    Measurable (Gf Xa Fl g) := by
  classical
  have hm := (IW.isOpen_dom X).measurableSet
  have h1 : Measurable (X.dom.piecewise g 0) := hg.measurable_piecewise continuousOn_const hm
  have h2 := ((h1.norm.pow_const 2).ennreal_ofReal).mul (WSk_meas Xa Fl)
  convert h2 using 1
  funext x
  by_cases hx : x ∈ X.dom
  · simp [Gf, hx]
  · simp [Gf, WSk, hx]

/- English proof (translation)
Establish `hq : 0 < ‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2` using `pow_pos (norm_pos_iff.2 (IW.bchar_ne_zero X hb _)) 2`. Establish `hq0 : ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2) ≠ 0`. Rewrite using `[Ne, ENNReal.ofReal_eq_zero, not_le]`. Conclude with `hq`. Unfold `Gf`.

Rewrite using `[(WSk_metric Xa Fl).2.1 x hx b hb, hg.2.1 x hx b hb, norm_mul, mul_pow, ENNReal.ofReal_mul hq.le, div_eq_mul_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Gf_rmul (Xa : ArchInM X) (Fl : FlatM X Xa) {g : Frame X.Ψ r → ℂ}
    (hg : X.IsSec (Xa.Fp + Xa.T • Xa.L) g) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {b : Frame X.Ψ r}
    (hb : b ∈ Bor X.Ψ r) : Gf Xa Fl g (rmul x b) = Gf Xa Fl g x := by
  have hq : 0 < ‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (IW.bchar_ne_zero X hb _)) 2
  have hq0 : ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2) ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le]; exact hq
  unfold Gf
  rw [(WSk_metric Xa Fl).2.1 x hx b hb, hg.2.1 x hx b hb, norm_mul, mul_pow,
    ENNReal.ofReal_mul hq.le, div_eq_mul_inv]
  calc ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2) * ENNReal.ofReal (‖g x‖ ^ 2) *
        (WSk X Xa Fl x * (ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2))⁻¹)
      = ENNReal.ofReal (‖g x‖ ^ 2) * WSk X Xa Fl x * (ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2) *
        (ENNReal.ofReal (‖bchar (Xa.Fp + Xa.T • Xa.L) b‖ ^ 2))⁻¹) := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel hq0 ENNReal.ofReal_ne_top, mul_one]

/- English proof (translation)
Unfold `Gf`. Rewrite using `[(WSk_metric Xa Fl).2.2 γ hγ x hx, hg.2.2 γ hγ x hx, norm_mul, OntoE.chi_norm X _ hγ, one_mul]`.
-/
theorem Gf_lact (Xa : ArchInM X) (Fl : FlatM X Xa) {g : Frame X.Ψ r → ℂ}
    (hg : X.IsSec (Xa.Fp + Xa.T • Xa.L) g) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) : Gf Xa Fl g (lact γ x) = Gf Xa Fl g x := by
  unfold Gf
  rw [(WSk_metric Xa Fl).2.2 γ hγ x hx, hg.2.2 γ hγ x hx, norm_mul, OntoE.chi_norm X _ hγ, one_mul]

/- English proof (translation)
Establish `hd : ∀ τ j, dmin X.Gm x τ j ≠ 0`. Introduce `τ j h`. Establish `h'` using `(hx τ).2 j`. Rewrite `h'` using `[h]`. Simplify using `at h'`.

Unfold `Data.nfac`. Conclude with `Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _`.
-/
private lemma nfac_pos_of_mem_dom {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la : Wt X.Ψ r) : 0 < X.nfac la x := by
  have hd : ∀ τ j, dmin X.Gm x τ j ≠ 0 := by
    intro τ j h
    have h' := (hx τ).2 j
    rw [h] at h'
    simp at h'
  unfold Data.nfac
  exact Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ =>
    Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _

/- English proof (translation)
Unfold `Data.nfac`. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.prod_pow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations.

Establish `hd : ∀ j, dmin X.Gm x τ j ≠ 0`. Introduce `j h`. Establish `h'` using `(hx τ).2 j`. Rewrite `h'` using `[h]`. Simplify using `at h'`.

Establish `hpos : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖` using `norm_pos_iff.mpr (div_ne_zero (hd _) (hd _))`. Establish `he : -(((la + T • L) τ i : ℤ) : ℝ) / 2 = -((la τ i : ℤ) : ℝ) / 2 + -((L τ i : ℤ) : ℝ) / 2 * (T : ℝ)`. Establish `h1 : ((la + T • L) τ i : ℤ) = la τ i + T • L τ i` using `rfl`. Rewrite using `[h1, nsmul_eq_mul]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[he, Real.rpow_add hpos, Real.rpow_mul hpos.le, Real.rpow_natCast]`.
-/
private lemma nfac_add_nsmul {x : Frame X.Ψ r} (hx : x ∈ X.dom) (la L : Wt X.Ψ r) (T : ℕ) :
    X.nfac (la + T • L) x = X.nfac la x * X.nfac L x ^ T := by
  unfold Data.nfac
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hd : ∀ j, dmin X.Gm x τ j ≠ 0 := by
    intro j h
    have h' := (hx τ).2 j
    rw [h] at h'
    simp at h'
  have hpos : 0 < ‖dmin X.Gm x τ i.succ / dmin X.Gm x τ i.castSucc‖ :=
    norm_pos_iff.mpr (div_ne_zero (hd _) (hd _))
  have he : -(((la + T • L) τ i : ℤ) : ℝ) / 2 =
      -((la τ i : ℤ) : ℝ) / 2 + -((L τ i : ℤ) : ℝ) / 2 * (T : ℝ) := by
    have h1 : ((la + T • L) τ i : ℤ) = la τ i + T • L τ i := rfl
    rw [h1, nsmul_eq_mul]
    push_cast
    ring
  rw [he, Real.rpow_add hpos, Real.rpow_mul hpos.le, Real.rpow_natCast]

/- English proof (translation)
Unfold `Gf WSk`. Rewrite using `[if_pos hx]`. Establish `hnn : 0 < X.nfac (Xa.Fp + Xa.T • Xa.L) x` using `nfac_pos_of_mem_dom hx _`. Establish `hexp : Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x) = X.nfac (Xa.Fp + Xa.T • Xa.L) x ^ 2`. Unfold `phla`.

Rewrite using `[show -(-2 * Real.log (X.nfac (Xa.Fp + Xa.T • Xa.L) x)) = Real.log (X.nfac (Xa.Fp + Xa.T • Xa.L) x) + Real.log (X.nfac (Xa.Fp + Xa.T • Xa.L) x) by ring, Real.exp_add, Real.exp_log hnn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hp : X.pnorm (Xa.Fp + Xa.T • Xa.L) g x ^ 2 = ‖g x‖ ^ 2 * X.nfac (Xa.Fp + Xa.T • Xa.L) x ^ 2` using `by show (‖g x‖ * X.nfac (Xa.Fp + Xa.T • Xa.L) x) ^ 2 = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hW : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2`.

Take `⟨k, hk⟩` from `Xa.w_nz x hx`. Establish `hk' : 0 < X.pnorm Xa.L (Xa.w k) x ^ 2`. Establish `: 0 < X.pnorm Xa.L (Xa.w k) x` using `mul_pos (norm_pos_iff.mpr hk) (nfac_pos_of_mem_dom hx _)`. Check the signs of the components of the expression. Conclude with `lt_of_lt_of_le hk' (Finset.single_le_sum (f := fun j => X.pnorm Xa.L (Xa.w j) x ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ k))`.

Establish `hS0 : 0 ≤ ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2` using `Finset.sum_nonneg fun k _ => sq_nonneg _`. Rewrite using `[hexp, hp, ENNReal.ofReal_rpow_of_pos hW]`. Use `set W := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hWd`. Use `set S := ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 with hSd`. Use `set n := X.nfac (Xa.Fp + Xa.T • Xa.L) x with hnd`.

Establish `hS : 0 < S`. Break down `hS0.lt_or_eq with h | h` into its components or cases. Conclude with `h`. Rewrite `hK` using `[← h, mul_zero]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hT : (1 / 2 : ℝ) ≤ (Xa.T : ℝ)`. Establish `h1 : 1 ≤ Xa.T`. Use `Xa.T_ge` as an intermediate fact. Use `Xa.n_ge` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `: (1 : ℝ) ≤ (Xa.T : ℝ)` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hratio : 1 / (max K 0 + 1) ≤ S / W`. Rewrite using `[div_le_div_iff₀ (by positivity) hW]`. Establish `: K * S ≤ max K 0 * S` using `mul_le_mul_of_nonneg_right (le_max_left _ _) hS0`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hA : ENNReal.ofReal (S / W) ^ (-((Xa.T : ℝ) - 1 / 2)) ≤ ENNReal.ofReal (1 / (max K 0 + 1)) ^ (-((Xa.T : ℝ) - 1 / 2))`. Rewrite using `[ENNReal.rpow_neg, ENNReal.rpow_neg]`. Conclude with `ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hratio) (by linarith))`. Rewrite using `[ENNReal.ofReal_mul (p := ‖g x‖ ^ 2 * n ^ 2) (by positivity), ENNReal.ofReal_mul (p := ‖g x‖ ^ 2) (by positivity)]`.

Establish `key` using `mul_le_mul_of_nonneg_left (a := ENNReal.ofReal (‖g x‖ ^ 2) * ENNReal.ofReal (n ^ 2) * ENNReal.ofReal (W ^ (-(Xa.T : ℝ)))) hA (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Gf_le_off (Xa : ArchInM X) (Fl : FlatM X Xa) (g : Frame X.Ψ r → ℂ) (K : ℝ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hK : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 ≤ K * ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2) :
    Gf Xa Fl g x ≤ ENNReal.ofReal (1 / (max K 0 + 1)) ^ (-((Xa.T : ℝ) - 1 / 2)) *
      ENNReal.ofReal (X.pnorm (Xa.Fp + Xa.T • Xa.L) g x ^ 2 *
        (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ (-(Xa.T : ℝ))) := by
  unfold Gf WSk
  rw [if_pos hx]
  have hnn : 0 < X.nfac (Xa.Fp + Xa.T • Xa.L) x := nfac_pos_of_mem_dom hx _
  have hexp : Real.exp (-phla X (Xa.Fp + Xa.T • Xa.L) x) = X.nfac (Xa.Fp + Xa.T • Xa.L) x ^ 2 := by
    unfold phla
    rw [show -(-2 * Real.log (X.nfac (Xa.Fp + Xa.T • Xa.L) x)) =
      Real.log (X.nfac (Xa.Fp + Xa.T • Xa.L) x) + Real.log (X.nfac (Xa.Fp + Xa.T • Xa.L) x) by ring,
      Real.exp_add, Real.exp_log hnn]
    ring
  have hp : X.pnorm (Xa.Fp + Xa.T • Xa.L) g x ^ 2 = ‖g x‖ ^ 2 * X.nfac (Xa.Fp + Xa.T • Xa.L) x ^ 2 := by
    show (‖g x‖ * X.nfac (Xa.Fp + Xa.T • Xa.L) x) ^ 2 = _
    ring
  have hW : 0 < ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 := by
    obtain ⟨k, hk⟩ := Xa.w_nz x hx
    have hk' : 0 < X.pnorm Xa.L (Xa.w k) x ^ 2 := by
      have : 0 < X.pnorm Xa.L (Xa.w k) x := mul_pos (norm_pos_iff.mpr hk) (nfac_pos_of_mem_dom hx _)
      positivity
    exact lt_of_lt_of_le hk' (Finset.single_le_sum (f := fun j => X.pnorm Xa.L (Xa.w j) x ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ k))
  have hS0 : 0 ≤ ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  rw [hexp, hp, ENNReal.ofReal_rpow_of_pos hW]
  set W := ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hWd
  set S := ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 with hSd
  set n := X.nfac (Xa.Fp + Xa.T • Xa.L) x with hnd
  have hS : 0 < S := by
    rcases hS0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hK
      linarith
  have hT : (1 / 2 : ℝ) ≤ (Xa.T : ℝ) := by
    have h1 : 1 ≤ Xa.T := by
      have := Xa.T_ge
      have := Xa.n_ge
      nlinarith
    have : (1 : ℝ) ≤ (Xa.T : ℝ) := by exact_mod_cast h1
    linarith
  have hratio : 1 / (max K 0 + 1) ≤ S / W := by
    rw [div_le_div_iff₀ (by positivity) hW]
    have : K * S ≤ max K 0 * S := mul_le_mul_of_nonneg_right (le_max_left _ _) hS0
    nlinarith
  have hA : ENNReal.ofReal (S / W) ^ (-((Xa.T : ℝ) - 1 / 2)) ≤
      ENNReal.ofReal (1 / (max K 0 + 1)) ^ (-((Xa.T : ℝ) - 1 / 2)) :=
    by
      rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
      exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hratio) (by linarith))
  rw [ENNReal.ofReal_mul (p := ‖g x‖ ^ 2 * n ^ 2) (by positivity),
    ENNReal.ofReal_mul (p := ‖g x‖ ^ 2) (by positivity)]
  have key := mul_le_mul_of_nonneg_left
    (a := ENNReal.ofReal (‖g x‖ ^ 2) * ENNReal.ofReal (n ^ 2) * ENNReal.ofReal (W ^ (-(Xa.T : ℝ)))) hA
    (by positivity)
  calc _ = ENNReal.ofReal (‖g x‖ ^ 2) * ENNReal.ofReal (n ^ 2) * ENNReal.ofReal (W ^ (-(Xa.T : ℝ))) *
        ENNReal.ofReal (S / W) ^ (-((Xa.T : ℝ) - 1 / 2)) := by ring
    _ ≤ _ := key
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OW

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter Metric
open scoped ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hc` using `Fl.coord j`. Establish `hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k => Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0` using `by filter_upwards [Filter.eventually_all.2 hcon] with z hz`. Simplify using `only [Pi.zero_apply] at hz`.

Simplify using `[hz]`. Both sides reduce to the same expression. Rewrite `hc` using `[hev.fderiv_eq, fderiv_const_apply]`. Apply `hc` to reduce the goal to its premises. Establish `h2` using `Xa.n_ge`.

Rewrite using `[ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero]`. Simplify using `only [finrank_euclideanSpace, Fintype.card_fin]`. Conclude with `zero_pow (by omega)`.
-/
theorem s_not_ev_zero {Xa : ArchInM X} (Fl : FlatM X Xa) (j : Fin Fl.δ) :
    ∃ k, ¬ (fun z => Fl.s k (cpt X (Fl.xs j) z)) =ᶠ[𝓝 (0 : V (nd X))] 0 := by
  by_contra hcon
  push_neg at hcon
  have hc := Fl.coord j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [Filter.eventually_all.2 hcon] with z hz
    simp only [Pi.zero_apply] at hz
    simp [hz]
    rfl
  rw [hev.fderiv_eq, fderiv_const_apply] at hc
  apply hc
  have h2 := Xa.n_ge
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero]
  simp only [finrank_euclideanSpace, Fintype.card_fin]
  exact zero_pow (by omega)

/- English proof (translation)
Establish `h1` using `Xa.T_ge`. Establish `h2 : nd X ≤ nd X ^ 2` using `Nat.le_self_pow two_ne_zero _`. Conclude with `h2.trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h1)`.
-/
theorem T_ge_n (Xa : ArchInM X) : nd X ≤ Xa.T := by
  have h1 := Xa.T_ge
  have h2 : nd X ≤ nd X ^ 2 := Nat.le_self_pow two_ne_zero _
  exact h2.trans (le_trans (Nat.le_mul_of_pos_left _ (by norm_num)) h1)

/- English proof (translation)
Establish `hn : 0 < X.nfac Xa.L x` using `nfac_pos_of_mem_dom hx Xa.L`. Establish `hnF : 0 < X.nfac Xa.Fp x` using `nfac_pos_of_mem_dom hx Xa.Fp`. Establish `hp : ∀ P : Frame X.Ψ r → ℂ, X.pnorm Xa.L P x ^ 2 = X.nfac Xa.L x ^ 2 * Complex.normSq (P x)`. Introduce `P`. Use `show (‖P x‖ * X.nfac Xa.L x) ^ 2 = _`.

Rewrite using `[Complex.normSq_eq_norm_sq]`. Expand and normalize the polynomial expressions, which then agree. Establish `hW : 0 < ∑ k, Complex.normSq (Xa.w k x)`. Take `⟨k, hk⟩` from `Xa.w_nz x hx`. Conclude with `lt_of_lt_of_le (Complex.normSq_pos.mpr hk) (Finset.single_le_sum (f := fun j => Complex.normSq (Xa.w j x)) (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ k))`.

Establish `sw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = X.nfac Xa.L x ^ 2 * ∑ k, Complex.normSq (Xa.w k x)`. Rewrite using `[Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => hp _`. Establish `ss : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = X.nfac Xa.L x ^ 2 * ∑ k, Complex.normSq (Fl.s k x)`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun k _ => hp _`. Establish `hnf : X.nfac (Xa.Fp + Xa.T • Xa.L) x = X.nfac Xa.Fp x * X.nfac Xa.L x ^ Xa.T` using `nfac_add_nsmul hx _ _ _`. Unfold `PsK phla`. Rewrite using `[sw, ss, hnf, mul_div_mul_left _ _ (pow_pos hn 2).ne', Real.rpow_def_of_pos hW, Real.rpow_def_of_pos hs, ← Real.exp_add, ← Real.exp_add]`. Use `congr 1`.

Rewrite using `[Real.log_mul (pow_pos hn 2).ne' hW.ne', Real.log_div hs.ne' hW.ne', Real.log_mul hnF.ne' (pow_pos hn _).ne']`. Simplify using `only [Real.log_pow]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exp_neg_PsK (Xa : ArchInM X) (Fl : FlatM X Xa) {x : Frame X.Ψ r} (hx : x ∈ X.dom)
    (hs : 0 < ∑ k, Complex.normSq (Fl.s k x)) :
    Real.exp (-PsK Xa Fl x) = Real.exp (-phla X Xa.Fp x) * (∑ k, Complex.normSq (Xa.w k x)) ^ (-(1 / 2 : ℝ)) *
      (∑ k, Complex.normSq (Fl.s k x)) ^ (-((Xa.T : ℝ) - 1 / 2)) := by
  have hn : 0 < X.nfac Xa.L x := nfac_pos_of_mem_dom hx Xa.L
  have hnF : 0 < X.nfac Xa.Fp x := nfac_pos_of_mem_dom hx Xa.Fp
  have hp : ∀ P : Frame X.Ψ r → ℂ,
      X.pnorm Xa.L P x ^ 2 = X.nfac Xa.L x ^ 2 * Complex.normSq (P x) := by
    intro P
    show (‖P x‖ * X.nfac Xa.L x) ^ 2 = _
    rw [Complex.normSq_eq_norm_sq]; ring
  have hW : 0 < ∑ k, Complex.normSq (Xa.w k x) := by
    obtain ⟨k, hk⟩ := Xa.w_nz x hx
    exact lt_of_lt_of_le (Complex.normSq_pos.mpr hk)
      (Finset.single_le_sum (f := fun j => Complex.normSq (Xa.w j x))
        (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ k))
  have sw : ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 = X.nfac Xa.L x ^ 2 * ∑ k, Complex.normSq (Xa.w k x) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hp _
  have ss : ∑ k, X.pnorm Xa.L (Fl.s k) x ^ 2 = X.nfac Xa.L x ^ 2 * ∑ k, Complex.normSq (Fl.s k x) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => hp _
  have hnf : X.nfac (Xa.Fp + Xa.T • Xa.L) x = X.nfac Xa.Fp x * X.nfac Xa.L x ^ Xa.T :=
    nfac_add_nsmul hx _ _ _
  unfold PsK phla
  rw [sw, ss, hnf, mul_div_mul_left _ _ (pow_pos hn 2).ne', Real.rpow_def_of_pos hW,
    Real.rpow_def_of_pos hs, ← Real.exp_add, ← Real.exp_add]
  congr 1
  rw [Real.log_mul (pow_pos hn 2).ne' hW.ne', Real.log_div hs.ne' hW.ne',
    Real.log_mul hnF.ne' (pow_pos hn _).ne']
  simp only [Real.log_pow]
  push_cast
  ring

/- English proof (translation)
Use `set c := cpt X (Fl.xs j) with hc`. Establish `hex : ((Xa.T - nd X : ℕ) : ℝ) + (nd X : ℝ) - 1 / 2 = (Xa.T : ℝ) - 1 / 2`. Rewrite using `[Nat.cast_sub (T_ge_n Xa)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hV` using `[hex]`.

Take `⟨k, hk⟩` from `s_not_ev_zero Fl j`. Establish `hbO : ball (0 : V (nd X)) ρ ⊆ OmF X (Fl.xs j)` using `ball_subset_closedBall.trans hsub`. Establish `hF : DifferentiableOn ℂ (fun z => Fl.s k (c z)) (ball (0 : V (nd X)) ρ)` using `(IW.comp_cpt_diffOn X (s_diffOn Fl k) (Fl.xs j)).mono hbO`. Establish `hnull` using `HE.zeros_null isOpen_ball hF (HE.hgn_of isOpen_ball (convex_ball _ _).isPreconnected hF (mem_ball_self hρ) hk)`. Establish `hQc : ContinuousOn (fun z => Real.exp (-phla X Xa.Fp (c z)) * (∑ k, Complex.normSq (Xa.w k (c z))) ^ (-(1 / 2 : ℝ))) (closedBall (0 : V (nd X)) ρ)`.

Introduce `z hz`. Establish `hzO` using `hsub hz`. Establish `h1` using `(IW.phla_cpt_cdAt X (Fl.xs j) hzO Xa.Fp).continuousAt`. Establish `h2` using `(sumSq_cdAt (ExF.isOpen_OmF X (Fl.xs j)) (fun k => IW.comp_cpt_diffOn X (w_diffOn Xa k) (Fl.xs j)) hzO).continuousAt`. Conclude with `((h1.neg.rexp).mul (h2.rpow_const (Or.inl (sumw_pos Xa hzO).ne'))).continuousWithinAt`.

Take `⟨C, hC⟩` from `(isCompact_closedBall (0 : V (nd X)) ρ).exists_bound_of_continuousOn hQc`. Establish `hC0 : 0 ≤ C` using `le_trans (norm_nonneg _) (hC 0 (mem_closedBall_self hρ.le))`. Establish `hae : ∀ᵐ z ∂(volume.restrict (ball (0 : V (nd X)) ρ)), Gf Xa Fl g (c z) ≤ ENNReal.ofReal C * ENNReal.ofReal (‖g (c z)‖ ^ 2 * (∑ k, ‖Fl.s k (c z)‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2)))`. Rewrite using `[ae_restrict_iff' measurableSet_ball]`. Use `filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz hzb`.

Establish `hFz : Fl.s k (c z) ≠ 0` using `fun h => hz ⟨hzb, h⟩`. Establish `hzO` using `hbO hzb`. Establish `hSp` using `sums_pos Fl hFz`. Establish `hQ` using `hC z (ball_subset_closedBall hzb)`. Rewrite `hQ` using `[Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) _))]`.

Unfold `Gf`. Rewrite using `[WSk_eq_exp Xa Fl hzO hSp, exp_neg_PsK Xa Fl hzO hSp, ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hC0]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Simplify using `only [Complex.sq_norm]`. Establish `hA : 0 ≤ Complex.normSq (g (c z)) * (∑ k, Complex.normSq (Fl.s k (c z))) ^ (-((Xa.T : ℝ) - 1 / 2))` using `mul_nonneg (Complex.normSq_nonneg _) (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) _)`.

Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ball_finite {Xa : ArchInM X} (Fl : FlatM X Xa) (g : Frame X.Ψ r → ℂ) (j : Fin Fl.δ)
    {ρV ρ : ℝ} (hρ : 0 < ρ) (hρV : ρ ≤ ρV)
    (hV : ∫⁻ z in ball (0 : V (nd X)) ρV, ENNReal.ofReal (‖g (cpt X (Fl.xs j) z)‖ ^ 2 *
      (∑ k, ‖Fl.s k (cpt X (Fl.xs j) z)‖ ^ 2) ^ (-(((Xa.T - nd X : ℕ) : ℝ) + (nd X : ℝ) - 1 / 2))) < ⊤)
    (hsub : closedBall (0 : V (nd X)) ρ ⊆ OmF X (Fl.xs j)) :
    ∫⁻ z in ball (0 : V (nd X)) ρ, Gf Xa Fl g (cpt X (Fl.xs j) z) < ⊤ := by
  set c := cpt X (Fl.xs j) with hc
  have hex : ((Xa.T - nd X : ℕ) : ℝ) + (nd X : ℝ) - 1 / 2 = (Xa.T : ℝ) - 1 / 2 := by
    rw [Nat.cast_sub (T_ge_n Xa)]; ring
  rw [hex] at hV
  obtain ⟨k, hk⟩ := s_not_ev_zero Fl j
  have hbO : ball (0 : V (nd X)) ρ ⊆ OmF X (Fl.xs j) := ball_subset_closedBall.trans hsub
  have hF : DifferentiableOn ℂ (fun z => Fl.s k (c z)) (ball (0 : V (nd X)) ρ) :=
    (IW.comp_cpt_diffOn X (s_diffOn Fl k) (Fl.xs j)).mono hbO
  have hnull := HE.zeros_null isOpen_ball hF
    (HE.hgn_of isOpen_ball (convex_ball _ _).isPreconnected hF (mem_ball_self hρ) hk)

  have hQc : ContinuousOn (fun z => Real.exp (-phla X Xa.Fp (c z)) *
      (∑ k, Complex.normSq (Xa.w k (c z))) ^ (-(1 / 2 : ℝ))) (closedBall (0 : V (nd X)) ρ) := by
    intro z hz
    have hzO := hsub hz
    have h1 := (IW.phla_cpt_cdAt X (Fl.xs j) hzO Xa.Fp).continuousAt
    have h2 := (sumSq_cdAt (ExF.isOpen_OmF X (Fl.xs j))
      (fun k => IW.comp_cpt_diffOn X (w_diffOn Xa k) (Fl.xs j)) hzO).continuousAt
    exact ((h1.neg.rexp).mul (h2.rpow_const (Or.inl (sumw_pos Xa hzO).ne'))).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : V (nd X)) ρ).exists_bound_of_continuousOn hQc
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 (mem_closedBall_self hρ.le))
  have hae : ∀ᵐ z ∂(volume.restrict (ball (0 : V (nd X)) ρ)), Gf Xa Fl g (c z) ≤
      ENNReal.ofReal C * ENNReal.ofReal (‖g (c z)‖ ^ 2 *
        (∑ k, ‖Fl.s k (c z)‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) := by
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with z hz hzb
    have hFz : Fl.s k (c z) ≠ 0 := fun h => hz ⟨hzb, h⟩
    have hzO := hbO hzb
    have hSp := sums_pos Fl hFz
    have hQ := hC z (ball_subset_closedBall hzb)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
      (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) _))] at hQ
    unfold Gf
    rw [WSk_eq_exp Xa Fl hzO hSp, exp_neg_PsK Xa Fl hzO hSp, ← ENNReal.ofReal_mul (sq_nonneg _),
      ← ENNReal.ofReal_mul hC0]
    apply ENNReal.ofReal_le_ofReal
    simp only [Complex.sq_norm]
    have hA : 0 ≤ Complex.normSq (g (c z)) * (∑ k, Complex.normSq (Fl.s k (c z))) ^ (-((Xa.T : ℝ) - 1 / 2)) :=
      mul_nonneg (Complex.normSq_nonneg _) (Real.rpow_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) _)
    calc Complex.normSq (g (c z)) * (Real.exp (-phla X Xa.Fp (c z)) * (∑ k, Complex.normSq (Xa.w k (c z))) ^ (-(1 / 2 : ℝ)) *
          (∑ k, Complex.normSq (Fl.s k (c z))) ^ (-((Xa.T : ℝ) - 1 / 2)))
        = (Real.exp (-phla X Xa.Fp (c z)) * (∑ k, Complex.normSq (Xa.w k (c z))) ^ (-(1 / 2 : ℝ))) *
          (Complex.normSq (g (c z)) * (∑ k, Complex.normSq (Fl.s k (c z))) ^ (-((Xa.T : ℝ) - 1 / 2))) := by ring
      _ ≤ C * (Complex.normSq (g (c z)) * (∑ k, Complex.normSq (Fl.s k (c z))) ^ (-((Xa.T : ℝ) - 1 / 2))) :=
        mul_le_mul_of_nonneg_right hQ hA
  calc ∫⁻ z in ball (0 : V (nd X)) ρ, Gf Xa Fl g (c z)
      ≤ ∫⁻ z in ball (0 : V (nd X)) ρ, ENNReal.ofReal C * ENNReal.ofReal (‖g (c z)‖ ^ 2 *
        (∑ k, ‖Fl.s k (c z)‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) := lintegral_mono_ae hae
    _ = ENNReal.ofReal C * ∫⁻ z in ball (0 : V (nd X)) ρ, ENNReal.ofReal (‖g (c z)‖ ^ 2 *
        (∑ k, ‖Fl.s k (c z)‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C * ∫⁻ z in ball (0 : V (nd X)) ρV, ENNReal.ofReal (‖g (c z)‖ ^ 2 *
        (∑ k, ‖Fl.s k (c z)‖ ^ 2) ^ (-((Xa.T : ℝ) - 1 / 2))) :=
        mul_le_mul' le_rfl (lintegral_mono_set (ball_subset_ball hρV))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OW
