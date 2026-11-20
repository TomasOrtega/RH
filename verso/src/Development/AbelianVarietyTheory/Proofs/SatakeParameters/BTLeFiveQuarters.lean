import Mathlib
import Formalism.SharpRestriction.ParConsts
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleFamilySizeRelationsEventuallyStatement

open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.Ggeo

/- English proof (translation)
Establish `hx1` using `L.sc.one_lt_alt`. Establish `hx : 0 < L.sc.x` using `lt_trans one_pos hx1`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hb' : 0 < L.sc.b'` using `div_pos (mul_pos hx hb) (Real.exp_pos _)`. Establish `hk : (0 : ℝ) < D.R.k`.

Use `D.R.m_add_three_le_k` as an intermediate fact. Conclude with `(by omega : 0 < D.R.k)` after adjusting the coercions. Establish `hLa : 0 ≤ L.LaG`. Establish `h1` using `P.S_le`. Establish `h2` using `L.Sc_pos`.

Establish `h3 : 0 < L.LaG * L.sc.b' / D.R.k` using `by linarith`. Establish `h4 : 0 < L.LaG * L.sc.b'` using `(div_pos_iff_of_pos_right hk).1 h3`. Conclude with `((mul_pos_iff_of_pos_right hb').1 h4).le`. Establish `hr` using `P.rho_le`. Establish `hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)`.

Establish `h5 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k` using `div_nonneg (mul_nonneg (mul_nonneg P.Crho_pos.le (Real.log_nonneg hx1.le)) hLa) hk.le`. Unfold `LevelStarExponents.rhoP at hr`. Establish `h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4`. Establish `: 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h7` using `P.bT_le t`. Establish `h8 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b'` using `by ring`. Establish `h9` using `mul_le_mul_of_nonneg_right h6 hb'.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bT_le_five_quarters {D : D7} {L : SizeData₂ D} (P : ParameterChoice' D L) (t : D.host.TT) :
    (L.bT t : ℝ) ≤ L.sc.b' + L.sc.b' / 4 := by
  have hx1 := L.sc.one_lt_alt
  have hx : 0 < L.sc.x := lt_trans one_pos hx1
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx hb) (Real.exp_pos _)
  have hk : (0 : ℝ) < D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < D.R.k)
  have hLa : 0 ≤ L.LaG := by
    have h1 := P.S_le
    have h2 := L.Sc_pos
    have h3 : 0 < L.LaG * L.sc.b' / D.R.k := by linarith
    have h4 : 0 < L.LaG * L.sc.b' := (div_pos_iff_of_pos_right hk).1 h3
    exact ((mul_pos_iff_of_pos_right hb').1 h4).le
  have hr := P.rho_le
  have hx2 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
  have h5 : 0 ≤ P.Crho * Real.log L.sc.x * L.LaG / D.R.k :=
    div_nonneg (mul_nonneg (mul_nonneg P.Crho_pos.le (Real.log_nonneg hx1.le)) hLa) hk.le
  unfold LevelStarExponents.rhoP at hr
  have h6 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 / 4 := by
    have : 4 * LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
        4 * (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
    linarith
  have h7 := P.bT_le t
  have h8 : LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
      (LevelStarExponents.Nstar L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) * L.sc.b' := by ring
  have h9 := mul_le_mul_of_nonneg_right h6 hb'.le
  linarith

/- English proof (translation)
Introduce `eps Fm`. Take `⟨x0, h0⟩` from `GlobalTheory.T.scale_family_size_relations_eventually Fm`. Use `⟨x0, fun x hx hx1 i j hj z => ?_⟩` and prove the remaining obligations. Take `⟨-, -, -, heta, hw, h4, h2b, -, -, -⟩` from `h0 x hx hx1 i`. Establish `P` using `Fm.params x hx1 i`.

Generalize the expression as in `Fm.L x i = L at *`. Generalize the expression as in `Fm.D x i = D at *`. Establish `hxp : 0 < L.sc.x` using `by linarith`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hb' : 0 < L.sc.b'` using `div_pos (mul_pos hxp hb) (Real.exp_pos _)`.

Establish `he` using `L.etaSz_pos`. Establish `hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4` using `div_le_div_of_nonneg_left hb'.le (by norm_num) h4`. Establish `hq0 : 0 < L.sc.b' / L.sc.x` using `div_pos hb' hxp`. Establish `htop : ∀ (τ : D.what₂.Tau) (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → L.sc.b' ≤ wj D (j + 1) τ ∧ wj D (j + 1) τ ≤ 2 * L.sc.b'`. Introduce `τ t ht`.

Take `⟨a1, a2⟩` from `L.win_top (j + 1) (by omega) (by omega) τ t ht`. Establish `a3` using `L.bT_ge t`. Establish `a4` using `bT_le_five_quarters P t`. Apply the tactic sequence `constructor <;> linarith`. Unfold `wPl`.

Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces`. Use `(L.win_thick (j + 1) (by omega) (by omega) _ h1).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces`.

Take `⟨t, ht, e⟩` from `Finset.mem_image.mp h2`. Use `(htop _ ⟨t, ht⟩ e.symm).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).1`. Distinguish the cases in `h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces`.

Conclude with `(L.win_thick (j + 1) (by omega) (by omega) _ h1).2`. Distinguish the cases in `h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces`. Take `⟨t, ht, e⟩` from `Finset.mem_image.mp h2`. Use `(htop _ ⟨t, ht⟩ e.symm).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Use `(L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce and unpack `⟨hz1, hz2⟩`. Use `htop _ ⟨z.2, hz2⟩ ?_` and prove the remaining obligations. Unfold `tauPl`.

Rewrite using `[Equiv.apply_symm_apply]`. Simplify using `[plGG, hz1]`.
-/
theorem wPl_windows : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 ∧ (IsTopPl (Fm.D x i) z → (Fm.L x i).sc.b' ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ 2 * (Fm.L x i).sc.b') := by
  intro eps Fm
  obtain ⟨x0, h0⟩ := GlobalTheory.T.scale_family_size_relations_eventually Fm
  refine ⟨x0, fun x hx hx1 i j hj z => ?_⟩
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, -, -⟩ := h0 x hx hx1 i
  have P := Fm.params x hx1 i
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have he := L.etaSz_pos
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) h4
  have hq0 : 0 < L.sc.b' / L.sc.x := div_pos hb' hxp
  have htop : ∀ (τ : D.what₂.Tau) (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t →
      L.sc.b' ≤ wj D (j + 1) τ ∧ wj D (j + 1) τ ≤ 2 * L.sc.b' := by
    intro τ t ht
    obtain ⟨a1, a2⟩ := L.win_top (j + 1) (by omega) (by omega) τ t ht
    have a3 := L.bT_ge t
    have a4 := bT_le_five_quarters P t
    constructor <;> linarith
  unfold wPl
  refine ⟨?_, ?_, ?_⟩
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · have := (L.win_thick (j + 1) (by omega) (by omega) _ h1).1
      linarith
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).1
      linarith
    · exact (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).1
  · by_cases h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces
    · exact (L.win_thick (j + 1) (by omega) (by omega) _ h1).2
    by_cases h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces
    · obtain ⟨t, ht, e⟩ := Finset.mem_image.mp h2
      have := (htop _ ⟨t, ht⟩ e.symm).2
      linarith
    · have := (L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).2
      linarith
  · rintro ⟨hz1, hz2⟩
    refine htop _ ⟨z.2, hz2⟩ ?_
    unfold tauPl
    rw [Equiv.apply_symm_apply]
    simp [plGG, hz1]

end GlobalTheory.Ggeo
