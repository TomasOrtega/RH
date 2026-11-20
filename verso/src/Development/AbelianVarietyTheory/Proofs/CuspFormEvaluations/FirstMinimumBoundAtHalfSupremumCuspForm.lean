import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.NegLogEpStar
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsRankOneCuspDataLogBoundsStatement

noncomputable section

namespace GlobalTheory.RunIn

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

/- English proof (translation)
Introduce `D T hL hG large₂ j hj w hP hL2 hr σ hσ f hf k z0 hz0 hmax hpos`. Establish `hr1 : 1 ≤ D.R.r`. Establish `h1` using `D.R.two_le_m`. Establish `h2` using `D.R.m_add_three_le_k`. Unfold `Formalism.BasicNotions.Ranks.r`.

Use linear arithmetic over natural numbers and integers. Establish `hSS : ∀ Q ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n), ∀ c, Q c ∈ ((T.U j σ).X c).SS (laU (T.U j σ) (wtA w) w.n c)`. Introduce `Q hQ`. Unfold `Formalism.L2.Pj.holSub at hQ`. Proceed by induction on `hQ using Submodule.span_induction with`.

Consider the case `mem x hx => intro c`. Conclude with `hx c`. Consider the case `zero`. Introduce `c`. Conclude with `⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero _ _ _ _ _⟩`.

Consider the case `add x y _ _ hx hy`. Introduce `c`. Take `⟨hx1, hx2⟩` from `hx c`. Take `⟨hy1, hy2⟩` from `hy c`. Use `⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add _ hx1 hy1, fun ξ hξ x' hx' => ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.add_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add _ hx1 hy1 hξ hx', hx2 ξ hξ x' hx', hy2 ξ hξ x' hx', add_zero]`. Consider the case `smul a x _ hx`. Introduce `c`. Take `⟨hx1, hx2⟩` from `hx c`. Use `⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul _ a hx1, fun ξ hξ x' hx' => ?_⟩` and prove the remaining obligations.

Rewrite using `[Pi.smul_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul, hx2 ξ hξ x' hx', mul_zero]`. Establish `hcusp : (rdU (T.U j σ)) f ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n)`. Unfold `Formalism.L2.Pj.Core.C at hf`. Conclude with `((Formalism.L2.Pj.mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n f).1 hf).2 σ hσ`. Establish `hPk` using `hSS _ hcusp k`.

Take `⟨e, M, wg, hM1, hMlog, hwg, _hwglog, hfwlog, hk⟩` from `GlobalTheory.T.exists_rankOne_cuspData_log_bounds D T hL hG large₂ j hj w hP hL2 hr σ hσ`. Take `⟨hspread, hflow, _hla, hNA, _hNC, _hg, hk0⟩` from `hk k`. Establish `hmb` using `ReciprocityTheory.ChartRestriction.G.FD.maxBound_holds D.R.r (e k).toX (laU (T.U j σ) (wtA w) w.n k) ((rdU (T.U j σ)) f k) M wg hPk (by linarith) hspread hwg hflow z0 hz0 hmax hpos`. Establish `hk0pos : 0 < (e k).k0` using `(e k).minWeight_pos`. Establish `hk0le : (e k).k0 ≤ 2` using `(e k).k0_le`.

Establish `hNApos : (0 : ℝ) < (e k).NA` using `by exact_mod_cast (e k).NA_pos`. Establish `hMpos : 0 < M` using `by linarith`. Establish `hfw : (0 : ℝ) < (fdeg D.host.E : ℝ) * wg + 2` using `by positivity`. Establish `hε : 0 < ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.epStar`.

Apply `lt_min one_pos` to reduce the goal to its premises. Apply `div_pos Real.pi_pos` to reduce the goal to its premises. Establish `hlog2 : 0 < Real.log 2` using `Real.log_pos one_lt_two`. Check the signs of the components of the expression. Establish `hc : ∀ τ : ((T.U j σ).X k).Ψ, ((T.U j σ).X k).c τ = (e k).k0`.

Introduce `τ`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.Data.c`. Rewrite using `[(e k).ξ0_abs τ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbpos : 0 < (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2` using `div_pos (mul_pos hk0pos hε) (pow_pos hNApos 2)`.

Establish `hlow : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤ ((T.U j σ).X k).firstMinimumSq z0`. Unfold `ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq`. Apply `le_csInf` to reduce the goal to its premises. Assume the negation of the conclusion as `hemp`. Rewrite `hemp` using `[Set.not_nonempty_iff_eq_empty]`.

Establish `h0 : ∀ v ∈ ((T.U j σ).X k).Λ, v = 0`. Introduce `v hv`. Assume the negation of the conclusion as `hv0`. Establish `hin : (∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) ∈ {t | ∃ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 ∧ t = ∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)}` using `⟨v, hv, hv0, rfl⟩`. Rewrite `hin` using `[hemp]`.

Conclude with `hin`. Establish `hbot : Submodule.span D.host.E (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = ⊥` using `Submodule.span_eq_bot.mpr h0`. Rewrite `hbot` using `[((T.U j σ).X k).Λ_span]`. Establish `hmem : (Pi.single (⟨0, hr1⟩ : Fin D.R.r) (1 : D.host.E)) ∈ (⊤ : Submodule D.host.E (Fin D.R.r → D.host.E))` using `Submodule.mem_top`. Rewrite `hmem` using `[hbot, Submodule.mem_bot]`.

Establish `h01` using `congrFun hmem ⟨0, hr1⟩`. Simplify using `at h01`. Introduce and unpack `t ⟨v, hv, hv0, rfl⟩`. Establish `hNAv : ((e k).NA : D.host.E) • v ∈ (e k).L'` using `(e k).NA_sub v hv`. Establish `hNAv0 : ((e k).NA : D.host.E) • v ≠ 0`.

Use `smul_ne_zero ?_ hv0` and prove the remaining obligations. Conclude with `(e k).NA_pos.ne'` after adjusting the coercions. Take `⟨τ0, hτ0⟩` from `hmb _ hNAv hNAv0`. Establish `hτ0' : ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 ≤ ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v))` using `hτ0`. Establish `hemb : ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v) = (Complex.ofReal ((e k).NA : ℝ)) • ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v`.

Use function extensionality and compare the values at `a`. Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.Data.emb]`. Rewrite `hτ0'` using `[hemb, ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_smul _ hz0 τ0 ((e k).NA : ℝ) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v)]`. Establish `hsum` using `Finset.single_le_sum (f := fun τ => ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) (fun τ _ => mul_nonneg (by rw [hc τ]; exact hk0pos.le) (ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.maj_nonneg _ hz0 τ _)) (Fins …`. Simplify using `only [hc τ0] at hsum`.

Establish `hstep : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤ (e k).k0 * ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v)`. Rewrite using `[mul_div_assoc]`. Apply `mul_le_mul_of_nonneg_left _ hk0pos.le` to reduce the goal to its premises. Rewrite using `[div_le_iff₀ (pow_pos hNApos 2)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Conclude with `le_trans hstep hsum`. Establish `hla1 : 0 < ((T.U j σ).X k).firstMinimumSq z0` using `lt_of_lt_of_le hbpos hlow`. Use `⟨hla1, ?_⟩` and prove the remaining obligations. Establish `h1 : Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤ Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2))` using `Real.log_le_log (one_div_pos.mpr hla1) (one_div_le_one_div_of_le hbpos hlow)`. Establish `hlog2 : Real.log 2 ≤ large₂.sc.L`.

Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hε'` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row.neg_log_epStar M (fdeg D.host.E) wg (e k).k0 hMpos hfw hk0pos hk0le`. Establish `hε2 : -Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0) ≤ 36 * large₂.sc.L`. Use `hε'.trans (max_le (by linarith) ?_)` and prove the remaining obligations.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1b : Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2)) = 2 * Real.log ((e k).NA : ℝ) + Real.log (1 / (e k).k0) - Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0)`. Rewrite using `[one_div_div, Real.log_div (pow_pos hNApos 2).ne' (mul_pos hk0pos hε).ne', Real.log_pow, Real.log_mul hk0pos.ne' hε.ne', one_div, Real.log_inv]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `h1` using `[h1b]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem firstMin_at_halfMax : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, ∀ (k : (T.U j σ).Comp), ∀ z0 ∈ ((T.U j σ).X k).dom, (∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x ≤ 2 * ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0) → 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z0 → 0 < ((T.U j σ).X k).firstMinimumSq z0 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤ 80 * large₂.sc.L := by
  intro D T hL hG large₂ j hj w hP hL2 hr σ hσ f hf k z0 hz0 hmax hpos

  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega

  have hSS : ∀ Q ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n), ∀ c,
      Q c ∈ ((T.U j σ).X c).SS (laU (T.U j σ) (wtA w) w.n c) := by
    intro Q hQ
    unfold Formalism.L2.Pj.holSub at hQ
    induction hQ using Submodule.span_induction with
    | mem x hx => intro c; exact hx c
    | zero =>
      intro c
      exact ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_zero _ _,
        fun ξ _ x _ => ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_zero _ _ _ _ _⟩
    | add x y _ _ hx hy =>
      intro c
      obtain ⟨hx1, hx2⟩ := hx c
      obtain ⟨hy1, hy2⟩ := hy c
      refine ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_add _ hx1 hy1, fun ξ hξ x' hx' => ?_⟩
      rw [Pi.add_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_add _ hx1 hy1 hξ hx', hx2 ξ hξ x' hx',
        hy2 ξ hξ x' hx', add_zero]
    | smul a x _ hx =>
      intro c
      obtain ⟨hx1, hx2⟩ := hx c
      refine ⟨ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_smul _ a hx1, fun ξ hξ x' hx' => ?_⟩
      rw [Pi.smul_apply, ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.fj_smul, hx2 ξ hξ x' hx', mul_zero]
  have hcusp : (rdU (T.U j σ)) f ∈ Formalism.L2.Pj.holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
    unfold Formalism.L2.Pj.Core.C at hf
    exact ((Formalism.L2.Pj.mem_cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n f).1 hf).2 σ hσ
  have hPk := hSS _ hcusp k
  obtain ⟨e, M, wg, hM1, hMlog, hwg, _hwglog, hfwlog, hk⟩ :=
    GlobalTheory.T.exists_rankOne_cuspData_log_bounds D T hL hG large₂ j hj w hP hL2 hr σ hσ
  obtain ⟨hspread, hflow, _hla, hNA, _hNC, _hg, hk0⟩ := hk k

  have hmb := ReciprocityTheory.ChartRestriction.G.FD.maxBound_holds D.R.r (e k).toX (laU (T.U j σ) (wtA w) w.n k)
    ((rdU (T.U j σ)) f k) M wg hPk (by linarith) hspread hwg hflow z0 hz0 hmax hpos
  have hk0pos : 0 < (e k).k0 := (e k).minWeight_pos
  have hk0le : (e k).k0 ≤ 2 := (e k).k0_le
  have hNApos : (0 : ℝ) < (e k).NA := by exact_mod_cast (e k).NA_pos
  have hMpos : 0 < M := by linarith
  have hfw : (0 : ℝ) < (fdeg D.host.E : ℝ) * wg + 2 := by positivity
  have hε : 0 < ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.epStar
    apply lt_min one_pos
    apply div_pos Real.pi_pos
    have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
    positivity

  have hc : ∀ τ : ((T.U j σ).X k).Ψ, ((T.U j σ).X k).c τ = (e k).k0 := by
    intro τ
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.c
    rw [(e k).ξ0_abs τ]
    ring

  have hbpos : 0 < (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 :=
    div_pos (mul_pos hk0pos hε) (pow_pos hNApos 2)
  have hlow : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤
      ((T.U j σ).X k).firstMinimumSq z0 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.firstMinimumSq
    apply le_csInf
    · by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      have h0 : ∀ v ∈ ((T.U j σ).X k).Λ, v = 0 := by
        intro v hv
        by_contra hv0
        have hin : (∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)) ∈
            {t | ∃ v ∈ ((T.U j σ).X k).Λ, v ≠ 0 ∧
              t = ∑ τ, ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v)} :=
          ⟨v, hv, hv0, rfl⟩
        rw [hemp] at hin
        exact hin
      have hbot : Submodule.span D.host.E (((T.U j σ).X k).Λ : Set (Fin D.R.r → D.host.E)) = ⊥ :=
        Submodule.span_eq_bot.mpr h0
      rw [((T.U j σ).X k).Λ_span] at hbot
      have hmem : (Pi.single (⟨0, hr1⟩ : Fin D.R.r) (1 : D.host.E)) ∈
          (⊤ : Submodule D.host.E (Fin D.R.r → D.host.E)) := Submodule.mem_top
      rw [hbot, Submodule.mem_bot] at hmem
      have h01 := congrFun hmem ⟨0, hr1⟩
      simp at h01
    · rintro t ⟨v, hv, hv0, rfl⟩
      have hNAv : ((e k).NA : D.host.E) • v ∈ (e k).L' := (e k).NA_sub v hv
      have hNAv0 : ((e k).NA : D.host.E) • v ≠ 0 := by
        refine smul_ne_zero ?_ hv0
        exact_mod_cast (e k).NA_pos.ne'
      obtain ⟨τ0, hτ0⟩ := hmb _ hNAv hNAv0
      have hτ0' : ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 ≤
          ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v)) := hτ0
      have hemb : ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 (((e k).NA : D.host.E) • v) =
          (Complex.ofReal ((e k).NA : ℝ)) • ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v := by
        funext a
        simp [ReciprocityTheory.ChartRestriction.G.FD.Data.emb]
      rw [hemb, ReciprocityTheory.ChartRestriction.G.FD.FlowMajorantFlags.maj_smul _ hz0 τ0 ((e k).NA : ℝ) (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v)] at hτ0'
      have hsum := Finset.single_le_sum
        (f := fun τ => ((T.U j σ).X k).c τ * ((T.U j σ).X k).maj z0 τ (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 v))
        (fun τ _ => mul_nonneg (by rw [hc τ]; exact hk0pos.le)
          (ReciprocityTheory.ChartRestriction.G.FD.FlagSpanBounds.maj_nonneg _ hz0 τ _)) (Finset.mem_univ τ0)
      simp only [hc τ0] at hsum
      have hstep : (e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2 ≤
          (e k).k0 * ((T.U j σ).X k).maj z0 τ0 (ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ0.1 v) := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left _ hk0pos.le
        rw [div_le_iff₀ (pow_pos hNApos 2)]
        linarith
      exact le_trans hstep hsum
  have hla1 : 0 < ((T.U j σ).X k).firstMinimumSq z0 := lt_of_lt_of_le hbpos hlow
  refine ⟨hla1, ?_⟩

  have h1 : Real.log (1 / ((T.U j σ).X k).firstMinimumSq z0) ≤
      Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2)) :=
    Real.log_le_log (one_div_pos.mpr hla1) (one_div_le_one_div_of_le hbpos hlow)
  have hlog2 : Real.log 2 ≤ large₂.sc.L := by
    have := Real.log_two_lt_d9
    linarith
  have hε' := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfLam1Row.neg_log_epStar M (fdeg D.host.E) wg (e k).k0 hMpos hfw hk0pos hk0le
  have hε2 : -Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0) ≤ 36 * large₂.sc.L := by
    refine hε'.trans (max_le (by linarith) ?_)
    linarith
  have h1b : Real.log (1 / ((e k).k0 * ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0 / ((e k).NA : ℝ) ^ 2)) =
      2 * Real.log ((e k).NA : ℝ) + Real.log (1 / (e k).k0) -
        Real.log (ReciprocityTheory.ChartRestriction.G.FD.epStar M (fdeg D.host.E) wg (e k).k0) := by
    rw [one_div_div, Real.log_div (pow_pos hNApos 2).ne' (mul_pos hk0pos hε).ne', Real.log_pow,
      Real.log_mul hk0pos.ne' hε.ne', one_div, Real.log_inv]
    push_cast
    ring
  rw [h1b] at h1
  linarith

end GlobalTheory.RunIn
