import Formalism.SharpRestriction.SmoothDesignExistence.ClosedLinkSOfClosedPeriodAndFiltration

noncomputable section

namespace Formalism.MainNotions.Pk.SD

open Formalism.BasicNotions Formalism.MainNotions.S

/- English proof (translation)
Establish `t1` using `@Formalism.MainNotions.S.standing_hypotheses_of_bounds`. Establish `t2` using `@Formalism.MainNotions.S.eps_pos'`. Establish `t3` using `@Formalism.MainNotions.S.sCl_le_CCount`. Establish `t4` using `@Formalism.MainNotions.S.sCl_pos`. Establish `t5` using `@Formalism.MainNotions.S.sCl_le_Cgap`.

Take `⟨h8, hTu, hRE⟩` from `hR`. Take `⟨x0, hx0⟩` from `hRE`. Take `⟨x2, hx2⟩` from `hTu`. Establish `hε` using `t2 Fm`. Establish `hs : 0 < eps / 100` using `by positivity`.

Take `⟨x3, hx3⟩` from `Filter.eventually_atTop.1 ((tendsto_rpow_atTop hs).eventually_ge_atTop (max (2 * sCl Fm) (max 2 (500 / eps))))`. Use `⟨max (max x0 x2) (max x3 (Fm.x1 + 1)), fun x hx i => ?_⟩` and prove the remaining obligations. Establish `hx1 : Fm.x1 < x`. Use `le_trans (le_max_right x3 (Fm.x1 + 1)) (le_max_right (max x0 x2) (max x3 (Fm.x1 + 1)))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hxa : x0 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `hxb : x2 ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `hxc : x3 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Establish `hXX : XX (Fm.L x i) = x ^ (eps / 100)`. Unfold `XX szTh`.

Rewrite using `[Fm.L_x x i hx1, Fm.L_eps]`. Establish `hB` using `hx3 x hxc`. Establish `hxr` using `hx0 x hxa i`. Establish `htu` using `hx2 x hxb i`. Establish `key` using `t1 (Fm.L x i) (Fm.params x hx1 i) (Fm.sizes x hx1 i) (sCl Fm) (1 / 2) Fm.CTu (t4 Fm)`.

Establish `hK` using `Fm.params_K x hx1 i`. Establish `eCkLow : (Fm.params x hx1 i).CkLow = Fm.CkLow` using `by first`. Consider the case `(unfold FamP.CkLow; rw [← hK]; rfl)`. Consider the case `simp [FamP.CkLow, ← hK, parConsts]`. Establish `eCCount : (Fm.params x hx1 i).CCount = Fm.CCount` using `by first`.

Consider the case `(unfold FamP.CCount; rw [← hK]; rfl)`. Consider the case `simp [FamP.CCount, ← hK, parConsts]`. Establish `eCgap : (Fm.params x hx1 i).Cgap = Fm.Cgap` using `by first`. Consider the case `(unfold FamP.Cgap; rw [← hK]; rfl)`. Consider the case `simp [FamP.Cgap, ← hK, parConsts]`.

Establish `eCYL : (Fm.params x hx1 i).CYL = Fm.CYL` using `by first`. Consider the case `(unfold FamP.CYL; rw [← hK]; rfl)`. Consider the case `simp [FamP.CYL, ← hK, parConsts]`. Use `show StandingHypotheses (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu`. Unfold `sC'`.

Rewrite using `[← eCkLow, ← eCYL]`. Use `key (eCCount ▸ t3 Fm) (eCgap ▸ t5 Fm) ?_ ?_ ?_ ?_ hxr.1 (Formalism.MainNotions.S.tuWin_of (Fm.L x i) Fm.CTu htu.1 htu.2)` and prove the remaining obligations. Rewrite using `[hXX]`. Conclude with `le_trans (le_max_left _ _) hB`. Rewrite using `[hXX]`.

Conclude with `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB`. Rewrite using `[hXX]`. Establish `h5 : 5 / szTh (Fm.L x i) = 500 / eps`. Unfold `szTh`. Rewrite using `[Fm.L_eps, div_div_eq_mul_div]`.

Evaluate the numerical expressions. Rewrite using `[h5]`. Conclude with `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB`. Rewrite using `[Fm.CGam_eq, eCkLow]`. Conclude with `h8`.
-/
theorem first_section_hypotheses_at_family_constants {eps : ℝ} (Fm : FamP eps) (hR : S.ResidualStandingConditions Fm) :
    OwnEv Fm fun C' Cl x i => StandingHypotheses (Fm.D x i) (Fm.L x i) C' Cl (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu := by
  have t1 := @Formalism.MainNotions.S.standing_hypotheses_of_bounds
  have t2 := @Formalism.MainNotions.S.eps_pos'
  have t3 := @Formalism.MainNotions.S.sCl_le_CCount
  have t4 := @Formalism.MainNotions.S.sCl_pos
  have t5 := @Formalism.MainNotions.S.sCl_le_Cgap
  obtain ⟨h8, hTu, hRE⟩ := hR
  obtain ⟨x0, hx0⟩ := hRE
  obtain ⟨x2, hx2⟩ := hTu
  have hε := t2 Fm
  have hs : 0 < eps / 100 := by positivity
  obtain ⟨x3, hx3⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop hs).eventually_ge_atTop (max (2 * sCl Fm) (max 2 (500 / eps))))
  refine ⟨max (max x0 x2) (max x3 (Fm.x1 + 1)), fun x hx i => ?_⟩
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_right x3 (Fm.x1 + 1)) (le_max_right (max x0 x2) (max x3 (Fm.x1 + 1)))
    linarith
  have hxa : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : x2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxc : x3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hXX : XX (Fm.L x i) = x ^ (eps / 100) := by
    unfold XX szTh
    rw [Fm.L_x x i hx1, Fm.L_eps]
  have hB := hx3 x hxc
  have hxr := hx0 x hxa i
  have htu := hx2 x hxb i
  have key := t1 (Fm.L x i) (Fm.params x hx1 i) (Fm.sizes x hx1 i) (sCl Fm) (1 / 2) Fm.CTu (t4 Fm)
  have hK := Fm.params_K x hx1 i
  have eCkLow : (Fm.params x hx1 i).CkLow = Fm.CkLow := by
    first
      | (unfold FamP.CkLow; rw [← hK]; rfl)
      | simp [FamP.CkLow, ← hK, parConsts]
  have eCCount : (Fm.params x hx1 i).CCount = Fm.CCount := by
    first
      | (unfold FamP.CCount; rw [← hK]; rfl)
      | simp [FamP.CCount, ← hK, parConsts]
  have eCgap : (Fm.params x hx1 i).Cgap = Fm.Cgap := by
    first
      | (unfold FamP.Cgap; rw [← hK]; rfl)
      | simp [FamP.Cgap, ← hK, parConsts]
  have eCYL : (Fm.params x hx1 i).CYL = Fm.CYL := by
    first
      | (unfold FamP.CYL; rw [← hK]; rfl)
      | simp [FamP.CYL, ← hK, parConsts]
  show StandingHypotheses (Fm.D x i) (Fm.L x i) (sC' Fm) (sCl Fm) (Fm.CYL + 1) (1 / 4) 3 (1 / 2) Fm.CTu
  unfold sC'
  rw [← eCkLow, ← eCYL]
  refine key (eCCount ▸ t3 Fm) (eCgap ▸ t5 Fm) ?_ ?_ ?_ ?_ hxr.1
    (Formalism.MainNotions.S.tuWin_of (Fm.L x i) Fm.CTu htu.1 htu.2)
  · rw [hXX]
    exact le_trans (le_max_left _ _) hB
  · rw [hXX]
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  · rw [hXX]
    have h5 : 5 / szTh (Fm.L x i) = 500 / eps := by
      unfold szTh
      rw [Fm.L_eps, div_div_eq_mul_div]
      norm_num
    rw [h5]
    exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  · rw [Fm.CGam_eq, eCkLow]; exact h8

end Formalism.MainNotions.Pk.SD

end
