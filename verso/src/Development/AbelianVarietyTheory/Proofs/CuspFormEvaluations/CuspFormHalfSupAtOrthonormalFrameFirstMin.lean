import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SupAtUnit
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FirstMinimumBoundAtHalfSupremumCuspFormStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

/- English proof (translation)
Introduce `D T hL hG large₂ j hj w hrows hL2 hn hlast σ hσ f hf hsup`. Establish `hfs : f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n` using `Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf`. Establish `hRS` using `(hL.unf j hj σ hσ).2.2.2.2.1 (wtA w) w.n (dom_wtA w) f hfs`. Unfold `Formalism.L2.Pj.supN at hsup ⊢`. Establish `hStop : Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≠ ⊤`.

Introduce `h`. Rewrite `hsup` using `[h]`. Simplify using `at hsup`. Establish `hSpos : 0 < Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)` using `(ENNReal.toReal_pos_iff.mp hsup).1`. Establish `hhalf` using `ENNReal.half_lt_self hSpos.ne' hStop`.

Establish `hhalf'` using `hhalf`. Unfold `Formalism.L2.Pj.supE at hhalf'`. Take `⟨⟨k, x, hx⟩, hp⟩` from `lt_iSup_iff.mp hhalf'`. Establish `hB` using `(hRS k).2.1`. Establish `hb` using `ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem ((T.U j σ).X k) hx`.

Establish `hy` using `ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom ((T.U j σ).X k) hx hb`. Establish `ho` using `ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf ((T.U j σ).X k) hx`. Establish `hpn` using `ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) hB x hx _ hb`. Establish `hu1 : ∀ τ i, ‖dmin ((T.U j σ).X k).Gm (rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf ((T.U j σ).X k) x)) τ i‖ = 1` using `fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho ((T.U j σ).X k) ho τ i`. Establish `hpu` using `ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) hu1`.

Establish `hrd` using `Formalism.L2.Pj.rdU_mem (T.U j σ) f k hy`. Establish `hlt` using `(ENNReal.toReal_lt_toReal (ENNReal.div_ne_top hStop two_ne_zero) ENNReal.ofReal_ne_top).mpr hp`. Rewrite `hlt` using `[ENNReal.toReal_div, ENNReal.toReal_ofReal']`. Establish `hlt' : (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal / 2 < max (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x) 0`. Simplify using `using hlt`.

Establish `hm : 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x`. Break down `lt_max_iff.mp (lt_trans (half_pos hsup) hlt') with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd h (lt_irrefl 0)`. Rewrite `hlt'` using `[max_eq_left hm.le]`.

Establish `hle : ∀ z ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z ≤ (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal`. Introduce `z hz`. Establish `h1 : ENNReal.ofReal (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z) ≤ Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)`. Unfold `Formalism.L2.Pj.supE`. Conclude with `le_iSup_of_le (⟨k, ⟨z, hz⟩⟩ : Formalism.L2.Pj.FPt (T.U j σ).X) le_rfl`.

Conclude with `(ENNReal.ofReal_le_iff_le_toReal hStop).mp h1`. Use `⟨k, ⟨_, hy⟩, hu1, ho, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hrd, ← hpu, hpn]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `GlobalTheory.T.firstMinimum_bound_at_halfSupremum_cuspForm D T hL hG large₂ j hj w hrows hL2 hn σ hσ f hf k _ hy (fun z hz => by rw [hpn]; linarith [hle z hz]) (by rw [hpn]; exact hm)`.
-/
theorem half_sup_at_ortho_frame : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, 0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) → ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧ supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤ 2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧ 0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 80 * large₂.sc.L := by
  intro D T hL hG large₂ j hj w hrows hL2 hn hlast σ hσ f hf hsup
  have hfs : f ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n := Formalism.L2.Pj.cusp_le_sec _ _ _ _ _ hf
  have hRS := (hL.unf j hj σ hσ).2.2.2.2.1 (wtA w) w.n (dom_wtA w) f hfs
  unfold Formalism.L2.Pj.supN at hsup ⊢
  have hStop : Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≠ ⊤ := by
    intro h
    rw [h] at hsup
    simp at hsup
  have hSpos : 0 < Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) :=
    (ENNReal.toReal_pos_iff.mp hsup).1
  have hhalf := ENNReal.half_lt_self hSpos.ne' hStop
  have hhalf' := hhalf
  unfold Formalism.L2.Pj.supE at hhalf'
  obtain ⟨⟨k, x, hx⟩, hp⟩ := lt_iSup_iff.mp hhalf'
  have hB := (hRS k).2.1
  have hb := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf_mem ((T.U j σ).X k) hx
  have hy := ReciprocityTheory.ChartRestriction.G.FD.OrthogonalFrameDomain.rmul_mem_dom ((T.U j σ).X k) hx hb
  have ho := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.ortho_bOf ((T.U j σ).X k) hx
  have hpn := ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.pnorm_rmul ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
    (rdU (T.U j σ) f k) hB x hx _ hb
  have hu1 : ∀ τ i, ‖dmin ((T.U j σ).X k).Gm
      (rmul x (ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.bOf ((T.U j σ).X k) x)) τ i‖ = 1 :=
    fun τ i => ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.dmin_ortho ((T.U j σ).X k) ho τ i
  have hpu := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfSupAtUnit.pnorm_unit ((T.U j σ).X k)
    (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) hu1
  have hrd := Formalism.L2.Pj.rdU_mem (T.U j σ) f k hy
  have hlt := (ENNReal.toReal_lt_toReal (ENNReal.div_ne_top hStop two_ne_zero)
    ENNReal.ofReal_ne_top).mpr hp
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal'] at hlt
  have hlt' : (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal / 2 <
      max (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x) 0 := by
    simpa using hlt
  have hm : 0 < ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) x := by
    rcases lt_max_iff.mp (lt_trans (half_pos hsup) hlt') with h | h
    · exact h
    · exact absurd h (lt_irrefl 0)
  rw [max_eq_left hm.le] at hlt'
  have hle : ∀ z ∈ ((T.U j σ).X k).dom,
      ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z ≤
        (Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f)).toReal := by
    intro z hz
    have h1 : ENNReal.ofReal (((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) (rdU (T.U j σ) f k) z) ≤
        Formalism.L2.Pj.supE (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) := by
      unfold Formalism.L2.Pj.supE
      exact le_iSup_of_le (⟨k, ⟨z, hz⟩⟩ : Formalism.L2.Pj.FPt (T.U j σ).X) le_rfl
    exact (ENNReal.ofReal_le_iff_le_toReal hStop).mp h1
  refine ⟨k, ⟨_, hy⟩, hu1, ho, ?_, ?_⟩
  · rw [← hrd, ← hpu, hpn]
    linarith
  · exact GlobalTheory.T.firstMinimum_bound_at_halfSupremum_cuspForm D T hL hG large₂ j hj w hrows hL2 hn σ hσ f hf k _ hy
      (fun z hz => by rw [hpn]; linarith [hle z hz]) (by rw [hpn]; exact hm)

end GlobalTheory.RunIn
