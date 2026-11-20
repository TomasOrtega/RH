import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SubMul

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Introduce `E _ _ _ H Dw x a a'`. Simplify using `only [Formalism.L2.Pj.lieFac, ← Real.exp_add]`. Use `congr 1`. Simplify using `only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lieFacAdd : LieFacAddSt := by
  intro E _ _ _ H Dw x a a'
  simp only [Formalism.L2.Pj.lieFac, ← Real.exp_add]
  congr 1
  simp only [Pi.add_apply, Nat.cast_add, Finset.sum_add_distrib]
  ring

/- English proof (translation)
Introduce `E _ _ _ r X la la' P Q x hx`. Establish `hne : ∀ τ j, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ j ≠ 0` using `fun τ j h => by`. Establish `h1` using `(hx τ).2 j`. Rewrite `h1` using `[h, Complex.zero_re, mul_zero]`. Conclude with `lt_irrefl 0 h1`.

Establish `hpos : ∀ τ (i : Fin r), 0 < ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖` using `fun τ i => norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))`. Establish `key : ∀ τ (i : Fin r), ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-((la + la') τ i : ℝ) / 2) = ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestrict …` using `fun τ i => by`. Rewrite using `[← Real.rpow_add (hpos τ i)]`. Use `congr 1`. Simplify using `only [Pi.add_apply]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Unfold `ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm`. Rewrite using `[Pi.mul_apply, norm_mul]`. Simplify using `only [key, Finset.prod_mul_distrib]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pnormMul : PnormMulSt := by
  intro E _ _ _ r X la la' P Q x hx
  have hne : ∀ τ j, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ j ≠ 0 := fun τ j h => by
    have h1 := (hx τ).2 j
    rw [h, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl 0 h1
  have hpos : ∀ τ (i : Fin r), 0 < ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ := fun τ i =>
    norm_pos_iff.2 (div_ne_zero (hne τ _) (hne τ _))
  have key : ∀ τ (i : Fin r), ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ /
      ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^ (-((la + la') τ i : ℝ) / 2) =
      ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la τ i : ℝ) / 2) *
        ‖ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.succ / ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i.castSucc‖ ^
          (-(la' τ i : ℝ) / 2) := fun τ i => by
    rw [← Real.rpow_add (hpos τ i)]
    congr 1
    simp only [Pi.add_apply]
    push_cast
    ring
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  rw [Pi.mul_apply, norm_mul]
  simp only [key, Finset.prod_mul_distrib]
  ring

/- English proof (translation)
The claim follows from `mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x)`.
-/
theorem pnorm_nonneg' {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (la : Wt X.Ψ r)
    (P : Frame X.Ψ r → ℂ) (x : Frame X.Ψ r) : 0 ≤ X.pnorm la P x :=
  mul_nonneg (norm_nonneg _) (Formalism.L2.Pj.pnorm_fac_nonneg X la x)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U x σ a a' n n' f g _ hn hn' hf hg`. Unfold `supC`. Rewrite using `[lieFacAdd E H Dw x a a', rdU_mul]`. Establish `hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n'`. Use function extensionality and compare the values at `fun k => laU_add (U σ) a a' n n' hn hn' k`.

Rewrite using `[hla]`. Establish `hE : Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g) ≤ Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) * Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g)`. Unfold `Formalism.L2.Pj.supE`. Use `iSup_le fun p => ?_` and prove the remaining obligations. Establish `e` using `pnormMul E r ((U σ).X p.1) (laU (U σ) a n p.1) (laU (U σ) a' n' p.1) (rdU (U σ) f p.1) (rdU (U σ) g p.1) p.2.1 p.2.2`.

Use `le_trans (le_of_eq ?_) (mul_le_mul' (le_iSup (fun q : FPt (U σ).X => ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a n q.1) (rdU (U σ) f q.1) q.2)) p) (le_iSup (fun q : FPt (U σ).X => ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a' n' q.1) (rdU (U σ) g q.1) q.2)) p))` and prove the remaining obligations. Rewrite using `[← ENNReal.ofReal_mul (pnorm_nonneg' _ _ _ _)]`. Conclude with `congrArg ENNReal.ofReal e`. Establish `h1` using `ENNReal.toReal_mono (ENNReal.mul_ne_top hf hg) hE`. Rewrite `h1` using `[ENNReal.toReal_mul]`.

Unfold `Formalism.L2.Pj.supN`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem supCMul : SupCMulSt := by
  intro E _ _ _ H Dw l Xo c r U x σ a a' n n' f g _ hn hn' hf hg
  unfold supC
  rw [lieFacAdd E H Dw x a a', rdU_mul]
  have hla : laU (U σ) (a + a') (n + n') = laU (U σ) a n + laU (U σ) a' n' :=
    funext fun k => laU_add (U σ) a a' n n' hn hn' k
  rw [hla]
  have hE : Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g) ≤
      Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) *
        Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g) := by
    unfold Formalism.L2.Pj.supE
    refine iSup_le fun p => ?_
    have e := pnormMul E r ((U σ).X p.1) (laU (U σ) a n p.1) (laU (U σ) a' n' p.1) (rdU (U σ) f p.1)
      (rdU (U σ) g p.1) p.2.1 p.2.2
    refine le_trans (le_of_eq ?_) (mul_le_mul' (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a n q.1) (rdU (U σ) f q.1) q.2)) p)
      (le_iSup (fun q : FPt (U σ).X =>
      ENNReal.ofReal (((U σ).X q.1).pnorm (laU (U σ) a' n' q.1) (rdU (U σ) g q.1) q.2)) p))
    rw [← ENNReal.ofReal_mul (pnorm_nonneg' _ _ _ _)]
    exact congrArg ENNReal.ofReal e
  have h1 := ENNReal.toReal_mono (ENNReal.mul_ne_top hf hg) hE
  rw [ENNReal.toReal_mul] at h1
  unfold Formalism.L2.Pj.supN
  calc lieFac Dw x a * lieFac Dw x a' *
        (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n + laU (U σ) a' n') (rdU (U σ) f * rdU (U σ) g)).toReal
      ≤ lieFac Dw x a * lieFac Dw x a' * ((Formalism.L2.Pj.supE (U σ).X (laU (U σ) a n) (rdU (U σ) f)).toReal *
          (Formalism.L2.Pj.supE (U σ).X (laU (U σ) a' n') (rdU (U σ) g)).toReal) :=
        mul_le_mul_of_nonneg_left h1 (mul_pos (lieFac_pos _ _ _) (lieFac_pos _ _ _)).le
    _ = _ := by ring

/- English proof (translation)
Introduce `D T h j hj σ w w' F G H hH`. Establish `hFm : (F : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n` using `cutR_le T.C j w F.2`. Establish `hGm : (G : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w') w'.n` using `cutR_le T.C j w' G.2`. Establish `hprod : (H : T.R j) = (F : T.R j) * (G : T.R j)`. Establish `h1` using `congrArg (fun x : AddMonoidAlgebra (T.R j) (Deg D j) => x.coeff (deg (Formalism.MainNotions.WeightAlgebra.wadd w w'))) hH`.

Express the relevant statement in the definitionally equal form `(incG deg (cutR T.C j) (Formalism.MainNotions.WeightAlgebra.wadd w w') H).coeff _ = (incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G).coeff _ at h1`. Rewrite `h1` using `[incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, ← deg_wadd]`. Simplify `h1` using `[AddMonoidAlgebra.coeff_single]`. Use `show cutN T.C T.Ns j (Formalism.MainNotions.WeightAlgebra.wadd w w') σ H ≤ cutN T.C T.Ns j w σ F * cutN T.C T.Ns j w' σ G`. Unfold `cutN`.

Rewrite using `[if_pos hj, if_pos hj, if_pos hj]`. Unfold `Core.Ns`. Rewrite using `[hprod, wtA_wadd]`. Conclude with `supCMul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (goodEmb_goodOf _ σ) w.n_even w'.n_even (supE_cusp_ne_top (goodEmb_goodOf _ σ) hFm) (supE_cusp_ne_top (goodEmb_goodOf _ σ) hGm)`.
-/
theorem recSubMul : RecSubMulSt := by
  intro D T h j hj σ w w' F G H hH
  have hFm : (F : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := cutR_le T.C j w F.2
  have hGm : (G : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w') w'.n := cutR_le T.C j w' G.2
  have hprod : (H : T.R j) = (F : T.R j) * (G : T.R j) := by
    have h1 := congrArg (fun x : AddMonoidAlgebra (T.R j) (Deg D j) => x.coeff (deg (Formalism.MainNotions.WeightAlgebra.wadd w w'))) hH
    change (incG deg (cutR T.C j) (Formalism.MainNotions.WeightAlgebra.wadd w w') H).coeff _ =
      (incG deg (cutR T.C j) w F * incG deg (cutR T.C j) w' G).coeff _ at h1
    rw [incG_apply, incG_apply, incG_apply, AddMonoidAlgebra.single_mul_single, ← deg_wadd] at h1
    simpa [AddMonoidAlgebra.coeff_single] using h1
  show cutN T.C T.Ns j (Formalism.MainNotions.WeightAlgebra.wadd w w') σ H ≤ cutN T.C T.Ns j w σ F * cutN T.C T.Ns j w' σ G
  unfold cutN
  rw [if_pos hj, if_pos hj, if_pos hj]
  unfold Core.Ns
  rw [hprod, wtA_wadd]
  exact supCMul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (goodEmb_goodOf _ σ) w.n_even w'.n_even
    (supE_cusp_ne_top (goodEmb_goodOf _ σ) hFm) (supE_cusp_ne_top (goodEmb_goodOf _ σ) hGm)

end ReciprocityTheory.ChartRestriction.G.PullbackSections
