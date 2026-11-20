import Mathlib
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CapLeWidth
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShapeUniform

def Big (eps x : ℝ) : Prop := 4 ≤ x ∧ x ^ 6 ≤ Real.exp (x ^ (eps / 3))

variable {eps : ℝ} (Fm : FamP eps) {x : ℝ}

/- English proof (translation)
Apply `GlobalTheory.ShNums.size_rel_at (Fm.L x i) (Fm.sizes x hx1 i)` to reduce the goal to its premises. Rewrite using `[Fm.L_x x i hx1]`. Conclude with `hg.1`. Unfold `Scale.X'`. Rewrite using `[Fm.L_x x i hx1, Fm.L_eps x i]`.

Conclude with `hg.2`.
-/
theorem size_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) :
    ((Fm.D x i).R.k : ℝ) * (Fm.D x i).R.N (Fm.D x i).R.m ≤ (Fm.L x i).Sc / 4 ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).Sc ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ ((Fm.D x i).R.m : ℝ) * (((Fm.D x i).R.t : ℝ) + 1) * (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.b' / (Fm.L x i).sc.x ∧ 4 ≤ (Fm.L x i).sc.x ∧ 2 * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ ((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b' ≤ (Fm.L x i).sc.b ∧ 1 ≤ (Fm.L x i).sc.w'' (Fm.D x i).R.n ∧ (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc ≤ (Fm.L x i).sc.b := by
  apply GlobalTheory.ShNums.size_rel_at (Fm.L x i) (Fm.sizes x hx1 i)
  · rw [Fm.L_x x i hx1]; exact hg.1
  · unfold Scale.X'
    rw [Fm.L_x x i hx1, Fm.L_eps x i]; exact hg.2

/- English proof (translation)
Introduce `j hj z`. Take `⟨-, -, -, heta, hw, h4, h2b, -, -, -⟩` from `size_at Fm hx1 i hg`. Establish `P` using `Fm.params x hx1 i`. Generalize the expression as in `Fm.L x i = L at *`. Generalize the expression as in `Fm.D x i = D at *`.

Establish `hxp : 0 < L.sc.x` using `by linarith`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hb' : 0 < L.sc.b'` using `div_pos (mul_pos hxp hb) (Real.exp_pos _)`. Establish `he` using `L.etaSz_pos`. Establish `hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4` using `div_le_div_of_nonneg_left hb'.le (by norm_num) h4`.

Establish `hq0 : 0 < L.sc.b' / L.sc.x` using `div_pos hb' hxp`. Establish `htop : ∀ (τ : D.what₂.Tau) (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → L.sc.b' ≤ wj D (j + 1) τ ∧ wj D (j + 1) τ ≤ 2 * L.sc.b'`. Introduce `τ t ht`. Take `⟨a1, a2⟩` from `L.win_top (j + 1) (by omega) (by omega) τ t ht`. Establish `a3` using `L.bT_ge t`.

Establish `a4` using `GlobalTheory.Ggeo.bT_le_five_quarters P t`. Apply the tactic sequence `constructor <;> linarith`. Unfold `wPl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces`.

Use `(L.win_thick (j + 1) (by omega) (by omega) _ h1).1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Distinguish the cases in `h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces`. Take `⟨t, ht, e⟩` from `Finset.mem_image.mp h2`. Use `(htop _ ⟨t, ht⟩ e.symm).1` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `(L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).1`. Distinguish the cases in `h1 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.thickPlaces`. Conclude with `(L.win_thick (j + 1) (by omega) (by omega) _ h1).2`. Distinguish the cases in `h2 : (D.eTau (tauPl D z) : D.R.GG) ∈ D.host.topPlaces`.

Take `⟨t, ht, e⟩` from `Finset.mem_image.mp h2`. Use `(htop _ ⟨t, ht⟩ e.symm).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `(L.win_thin (j + 1) (by omega) (by omega) _ ⟨(D.eTau _).2, h2, h1⟩).2` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Introduce and unpack `⟨hz1, hz2⟩`. Use `htop _ ⟨z.2, hz2⟩ ?_` and prove the remaining obligations. Unfold `tauPl`. Rewrite using `[Equiv.apply_symm_apply]`. Simplify using `[plGG, hz1]`.
-/
theorem windows_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (Fm.L x i).sc.w'' (Fm.D x i).R.n ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 ∧ (IsTopPl (Fm.D x i) z → (Fm.L x i).sc.b' ≤ wPl (Fm.D x i) (j + 1) z ∧ wPl (Fm.D x i) (j + 1) z ≤ 2 * (Fm.L x i).sc.b') := by
  intro j hj z
  obtain ⟨-, -, -, heta, hw, h4, h2b, -, -, -⟩ := size_at Fm hx1 i hg
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
    have a4 := GlobalTheory.Ggeo.bT_le_five_quarters P t
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

/- English proof (translation)
Introduce `u j hj z r hr`. Take `⟨h1, h2⟩` from `GlobalTheory.LongRows.row_bounds (Fm.D x i) u j hj z r hr`. Use `⟨fun hz => ?_, fun _ hr1 hr2 => ?_⟩` and prove the remaining obligations. Take `⟨h3, h4⟩` from `GlobalTheory.LongRows.u_bounds_off (Fm.params x hx i) u _ (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) r hr`. Apply the tactic sequence `constructor <;> linarith`.

Take `⟨h3, h4⟩` from `(Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨r, hr⟩ hr1 hr2`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem long_at (hx : Fm.x1 < x) (i : Fm.Ix x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ∀ r < (Fm.D x i).R.k, (¬ IsTopPl (Fm.D x i) z → wPl (Fm.D x i) (j + 1) z - (Fm.D x i).R.N (Fm.D x i).R.m - 1 / 2 < DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r < wPl (Fm.D x i) (j + 1) z + (if r = 0 then 3 * (Fm.L x i).Sc else (Fm.L x i).Sc)) ∧ (IsTopPl (Fm.D x i) z → 1 ≤ r → r + 1 < (Fm.D x i).R.k → wPl (Fm.D x i) (j + 1) z - (Fm.D x i).R.N (Fm.D x i).R.m < DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r < wPl (Fm.D x i) (j + 1) z + (Fm.L x i).Sc) := by
  intro u j hj z r hr
  obtain ⟨h1, h2⟩ := GlobalTheory.LongRows.row_bounds (Fm.D x i) u j hj z r hr
  refine ⟨fun hz => ?_, fun _ hr1 hr2 => ?_⟩
  · obtain ⟨h3, h4⟩ := GlobalTheory.LongRows.u_bounds_off (Fm.params x hx i) u _ (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) r hr
    constructor <;> linarith
  · obtain ⟨h3, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨r, hr⟩ hr1 hr2
    constructor <;> linarith

/- English proof (translation)
Introduce `u j hj z r hk hr`. Use `⟨(RowWeightLemmas.nuRow_pos _ u j hj _ r hr).le, ?_⟩` and prove the remaining obligations. Take `⟨q, s, hq, hs, rfl⟩` from `RowWeightLemmas.block_decomp _ j r hk hr`. Rewrite using `[RowWeightLemmas.nuRow_block _ u j hj _ q s hq hs, (Fm.D x i).hcW_e u]`. Establish `h1` using `(Fm.L x i).be_close (tauPl (Fm.D x i) z) ⟨q, by omega⟩ ⟨j, hj⟩`.

Establish `h2` using `((Fm.D x i).hc (tauPl (Fm.D x i) z)).gap_be ⟨q, by omega⟩`. Establish `h3 : (0 : ℚ) ≤ ((j : ℚ) - q) * (((Fm.D x i).R.t : ℚ) + 1)`. Establish `: (q : ℚ) ≤ j` using `by exact_mod_cast hq.le`. Conclude with `mul_nonneg (by linarith) (by positivity)`. Establish `h4 : (0 : ℚ) ≤ (((Fm.D x i).R.t : ℚ) + 3) / 2` using `by positivity`.

Use `le_trans ?_ h1` and prove the remaining obligations. Use `le_trans ?_ (neg_le_abs _)` and prove the remaining obligations. Rewrite using `[← Rat.cast_neg]`. Conclude with `Rat.cast_le.2 (by linarith)`.
-/
theorem block_at (i : Fm.Ix x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ∀ r, (Fm.D x i).R.k ≤ r → r < (Fm.D x i).R.N j → 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ≤ (Fm.L x i).etaSz := by
  intro u j hj z r hk hr
  refine ⟨(RowWeightLemmas.nuRow_pos _ u j hj _ r hr).le, ?_⟩
  obtain ⟨q, s, hq, hs, rfl⟩ := RowWeightLemmas.block_decomp _ j r hk hr
  rw [RowWeightLemmas.nuRow_block _ u j hj _ q s hq hs, (Fm.D x i).hcW_e u]
  have h1 := (Fm.L x i).be_close (tauPl (Fm.D x i) z) ⟨q, by omega⟩ ⟨j, hj⟩
  have h2 := ((Fm.D x i).hc (tauPl (Fm.D x i) z)).gap_be ⟨q, by omega⟩
  have h3 : (0 : ℚ) ≤ ((j : ℚ) - q) * (((Fm.D x i).R.t : ℚ) + 1) := by
    have : (q : ℚ) ≤ j := by exact_mod_cast hq.le
    exact mul_nonneg (by linarith) (by positivity)
  have h4 : (0 : ℚ) ≤ (((Fm.D x i).R.t : ℚ) + 3) / 2 := by positivity
  refine le_trans ?_ h1
  refine le_trans ?_ (neg_le_abs _)
  rw [← Rat.cast_neg]
  exact Rat.cast_le.2 (by linarith)

/- English proof (translation)
Introduce `u j hj z hz`. Establish `h4` using `GlobalTheory.TopRows.eta_le (Fm.params x hx1 i)`. Take `⟨e1, e2, e3, e4⟩` from `GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj z hz`. Use `⟨e1, e2, e3, e4.trans ?_⟩` and prove the remaining obligations. Rewrite using `[mul_div_assoc]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem top_rows_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) 0 = (aL (Fm.L x i) z.2 : ℝ) + (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) = (wPl (Fm.D x i) (j + 1) z - kaJ (Fm.D x i) (j + 1)) - (bL (Fm.L x i) z.2 : ℝ) ∧ 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) ((Fm.D x i).R.k - 1) ≤ 2 * (Fm.L x i).sc.b' / (Fm.L x i).sc.x := by
  intro u j hj z hz
  have h4 := GlobalTheory.TopRows.eta_le (Fm.params x hx1 i)
  obtain ⟨e1, e2, e3, e4⟩ := GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj z hz
  refine ⟨e1, e2, e3, e4.trans ?_⟩
  rw [mul_div_assoc]
  linarith

/- English proof (translation)
Introduce `u j hj τ l hl`. Establish `hS` using `Fm.sizes x hx1 i`. Establish `hsx : (Fm.L x i).sc.x = x` using `Fm.L_x x i hx1`. Establish `h2x : 2 ≤ (Fm.L x i).sc.x` using `by rw [hsx]; exact hx2`. Take `⟨h1j, hmj⟩` from `Finset.mem_Icc.1 hj`.

Take `⟨a1, hw3⟩` from `GlobalTheory.HCEntries.wj_bounds hS h2x j h1j hmj τ`. Establish `hwe : DV.wSz (Fm.D x i) j τ = wj (Fm.D x i) j τ`. Unfold `DV.wSz wj`. Rewrite using `[dif_pos ⟨h1j, hmj⟩, dif_pos (by omega)]`. Establish `hj'` using `Finset.mem_Icc.1 hj`.

Take `⟨j', rfl⟩ : ∃ j', j = j' + 1` from `⟨j - 1, by omega⟩`. Establish `hl' : l < (Fm.D x i).R.N j'` using `by simpa using hl`. Establish `hjm : j' < (Fm.D x i).R.m` using `by omega`. Establish `hk : 0 < (Fm.D x i).R.k` using `by have := (Fm.D x i).R.m_add_three_le_k; omega`. Use `⟨(RowWeightLemmas.nuRow_pos _ u j' hjm τ l hl').le, ?_⟩` and prove the remaining obligations.

Establish `h1` using `RowWeightLemmas.nuRow_anti' _ u j' hjm τ l 0 (Nat.zero_le _) hl'`. Establish `h2` using `GlobalTheory.nuRow_zero_le (Fm.D x i) u (j' + 1) τ hk`. Establish `hu : |((((Fm.D x i).hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ)| ≤ 4 * x * (Fm.L x i).sc.b`. Use `GlobalTheory.HCEntries.u_bound hS (Fm.params x hx1 i) h2x u τ ⟨0, hk⟩` as an intermediate fact. Rewrite `this` using `[hsx]`. Then use the resulting hypothesis.

Establish `h3` using `(abs_le.1 hu).2`. Establish `hb : 0 < (Fm.L x i).sc.b` using `Real.exp_pos _`. Establish `hx' : 1 < x` using `Fm.one_lt_family_threshold.trans hx1`. Establish `h4 : (Fm.L x i).sc.b ≤ x * (Fm.L x i).sc.b` using `le_mul_of_one_le_left hb.le hx'.le`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem nuRow_le_at (hx2 : 2 ≤ x) (hx1 : Fm.x1 < x) (i : Fm.Ix x) : ∀ u, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ τ, ∀ l < (Fm.D x i).R.N (j - 1), 0 ≤ DV.nuRow (Fm.D x i) u j τ l ∧ DV.nuRow (Fm.D x i) u j τ l ≤ 10 * x * (Fm.L x i).sc.b := by
  intro u j hj τ l hl
  have hS := Fm.sizes x hx1 i
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have h2x : 2 ≤ (Fm.L x i).sc.x := by rw [hsx]; exact hx2
  obtain ⟨h1j, hmj⟩ := Finset.mem_Icc.1 hj
  obtain ⟨a1, hw3⟩ := GlobalTheory.HCEntries.wj_bounds hS h2x j h1j hmj τ
  have hwe : DV.wSz (Fm.D x i) j τ = wj (Fm.D x i) j τ := by
    unfold DV.wSz wj
    rw [dif_pos ⟨h1j, hmj⟩, dif_pos (by omega)]
  have hj' := Finset.mem_Icc.1 hj
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hl' : l < (Fm.D x i).R.N j' := by simpa using hl
  have hjm : j' < (Fm.D x i).R.m := by omega
  have hk : 0 < (Fm.D x i).R.k := by have := (Fm.D x i).R.m_add_three_le_k; omega
  refine ⟨(RowWeightLemmas.nuRow_pos _ u j' hjm τ l hl').le, ?_⟩
  have h1 := RowWeightLemmas.nuRow_anti' _ u j' hjm τ l 0 (Nat.zero_le _) hl'
  have h2 := GlobalTheory.nuRow_zero_le (Fm.D x i) u (j' + 1) τ hk
  have hu : |((((Fm.D x i).hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ)| ≤ 4 * x * (Fm.L x i).sc.b := by
    have := GlobalTheory.HCEntries.u_bound hS (Fm.params x hx1 i) h2x u τ ⟨0, hk⟩
    rwa [hsx] at this
  have h3 := (abs_le.1 hu).2
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hx' : 1 < x := Fm.one_lt_family_threshold.trans hx1
  have h4 : (Fm.L x i).sc.b ≤ x * (Fm.L x i).sc.b := le_mul_of_one_le_left hb.le hx'.le
  nlinarith

/- English proof (translation)
Introduce `u j hj z hz`. Take `⟨a1, a2, a3, -⟩` from `size_at Fm hx1 i hg`. Establish `hk` using `(Fm.D x i).R.m_add_three_le_k`. Rewrite using `[GlobalTheory.nuD_card_eq_sum_nuRow (Fm.D x i) (nuRowOK _) u j hj z]`. Establish `heta` using `(Fm.L x i).etaSz_pos`.

Use `GlobalTheory.ExcessLow.excess_sum _ (Fm.D x i).R.k (j * ((Fm.D x i).R.t + 1)) _ ((Fm.D x i).R.N (Fm.D x i).R.m) (Fm.L x i).Sc (Fm.L x i).etaSz ((Fm.L x i).sc.w'' (Fm.D x i).R.n) (by omega) ?_ (Fm.L x i).Sc_pos.le (fun r hr => (long_at Fm hx1 i u j hj z r hr).1 hz) (fun r hr hr' = …` and prove the remaining obligations. Establish `: 1 ≤ (Fm.D x i).R.N (Fm.D x i).R.m`. Unfold `Ranks.N`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions.

Use `le_trans ?_ a3` and prove the remaining obligations. Apply `mul_le_mul_of_nonneg_right _ heta.le` to reduce the goal to its premises. Use `push_cast`. Establish `: (j : ℝ) ≤ (Fm.D x i).R.m` using `by exact_mod_cast hj.le`. Conclude with `mul_le_mul_of_nonneg_right this (by positivity)`.
-/
theorem excess_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ¬ IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro u j hj z hz
  obtain ⟨a1, a2, a3, -⟩ := size_at Fm hx1 i hg
  have hk := (Fm.D x i).R.m_add_three_le_k
  rw [GlobalTheory.nuD_card_eq_sum_nuRow (Fm.D x i) (nuRowOK _) u j hj z]
  have heta := (Fm.L x i).etaSz_pos
  refine GlobalTheory.ExcessLow.excess_sum _ (Fm.D x i).R.k (j * ((Fm.D x i).R.t + 1)) _
    ((Fm.D x i).R.N (Fm.D x i).R.m) (Fm.L x i).Sc (Fm.L x i).etaSz
    ((Fm.L x i).sc.w'' (Fm.D x i).R.n) (by omega) ?_ (Fm.L x i).Sc_pos.le
    (fun r hr => (long_at Fm hx1 i u j hj z r hr).1 hz)
    (fun r hr hr' => block_at Fm i u j hj z r hr hr') a1 a2 ?_ (windows_at Fm hx1 i hg j hj z).1
  · have : 1 ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      omega
    exact_mod_cast this
  · refine le_trans ?_ a3
    apply mul_le_mul_of_nonneg_right _ heta.le
    push_cast
    have : (j : ℝ) ≤ (Fm.D x i).R.m := by exact_mod_cast hj.le
    exact mul_le_mul_of_nonneg_right this (by positivity)

/- English proof (translation)
Introduce `u j hj z hz`. Take `⟨a1, a2, a3, -, a5, a6, -, -, a9, -⟩` from `size_at Fm hx1 i hg`. Take `⟨b1, -, b3⟩` from `windows_at Fm hx1 i hg j hj z`. Take `⟨b3, -⟩` from `b3 hz`. Establish `c` using `long_at Fm hx1 i u j hj z`.

Take `⟨-, -, d3, d4⟩` from `top_rows_at Fm hx1 i u j hj z hz`. Establish `e` using `block_at Fm i u j hj z`. Generalize the expression as in `Fm.L x i = L at *`. Generalize the expression as in `Fm.D x i = D at *`. Establish `hk : 5 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`.

Establish `hN : D.R.N j = D.R.k + j * (D.R.t + 1)` using `by unfold Ranks.N; omega`. Establish `hok` using `nuRowOK D`. Rewrite using `[GlobalTheory.nuD_card_eq_sum_nuRow D hok u j hj z, hok u j hj z 0, if_pos (by omega), hN, GlobalTheory.TopExcess.sum_range_split _ _ _ (by omega)]`. Take `⟨m1, m2⟩` from `GlobalTheory.TopExcess.sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) 1 (D.R.k - 1) _ _ (fun r hr1 hr2 => let h := (c r (by omega)).2 hz hr1 (by omega); ⟨h.1.le, h.2.le⟩)`. Take `⟨n1, n2⟩` from `GlobalTheory.TopExcess.sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) D.R.k (D.R.k + j * (D.R.t + 1)) _ _ (fun r hr1 hr2 => e r hr1 (by omega))`.

Establish `hkc : ((D.R.k - 1 - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 2`. Rewrite using `[Nat.sub_sub, Nat.cast_sub (by omega)]; norm_num`. Rewrite `m1`, `m2` using `[hkc]`. Rewrite `n1`, `n2` using `[Nat.add_sub_cancel_left]`. Move the coercions through the operations in `at n1 n2`.

Establish `hS` using `L.Sc_pos`. Establish `he` using `L.etaSz_pos`. Establish `hk' : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk`. Establish `hj' : (j : ℝ) ≤ D.R.m` using `by exact_mod_cast hj.le`. Establish `ht : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`.

Establish `hNm : (0 : ℝ) ≤ D.R.N D.R.m` using `Nat.cast_nonneg _`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hb' : 0 < L.sc.b'` using `div_pos (mul_pos hx0 hb) (Real.exp_pos _)`. Establish `hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4` using `div_le_div_of_nonneg_left hb'.le (by norm_num) a6`.

Establish `hbl : (j : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz` using `by gcongr`. Establish `hS1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc` using `le_mul_of_one_le_left hS.le (by linarith)`. Rewrite `d4` using `[mul_div_assoc]`. Apply the tactic sequence `constructor <;> nlinarith`.
-/
theorem top_excess_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 0 ≤ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ∧ (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) - (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) - ((((Fm.D x i).R.k : ℝ) - 1) * wPl (Fm.D x i) (j + 1) z - 2 * wPl (Fm.D x i) (j + 1) z) ≤ 4 * wPl (Fm.D x i) (j + 1) z := by
  intro u j hj z hz
  obtain ⟨a1, a2, a3, -, a5, a6, -, -, a9, -⟩ := size_at Fm hx1 i hg
  obtain ⟨b1, -, b3⟩ := windows_at Fm hx1 i hg j hj z
  obtain ⟨b3, -⟩ := b3 hz
  have c := long_at Fm hx1 i u j hj z
  obtain ⟨-, -, d3, d4⟩ := top_rows_at Fm hx1 i u j hj z hz
  have e := block_at Fm i u j hj z
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hN : D.R.N j = D.R.k + j * (D.R.t + 1) := by unfold Ranks.N; omega
  have hok := nuRowOK D
  rw [GlobalTheory.nuD_card_eq_sum_nuRow D hok u j hj z, hok u j hj z 0, if_pos (by omega), hN,
    GlobalTheory.TopExcess.sum_range_split _ _ _ (by omega)]
  obtain ⟨m1, m2⟩ := GlobalTheory.TopExcess.sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) 1 (D.R.k - 1) _ _
    (fun r hr1 hr2 => let h := (c r (by omega)).2 hz hr1 (by omega); ⟨h.1.le, h.2.le⟩)
  obtain ⟨n1, n2⟩ := GlobalTheory.TopExcess.sum_Ico_bounds (DV.nuRow D u (j + 1) (tauPl D z)) D.R.k (D.R.k + j * (D.R.t + 1)) _ _
    (fun r hr1 hr2 => e r hr1 (by omega))
  have hkc : ((D.R.k - 1 - 1 : ℕ) : ℝ) = (D.R.k : ℝ) - 2 := by
    rw [Nat.sub_sub, Nat.cast_sub (by omega)]; norm_num
  rw [hkc] at m1 m2
  rw [Nat.add_sub_cancel_left] at n1 n2
  push_cast at n1 n2
  have hS := L.Sc_pos
  have he := L.etaSz_pos
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hj' : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj.le
  have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
  have hNm : (0 : ℝ) ≤ D.R.N D.R.m := Nat.cast_nonneg _
  have hx0 : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hx0 hb) (Real.exp_pos _)
  have hq : L.sc.b' / L.sc.x ≤ L.sc.b' / 4 := div_le_div_of_nonneg_left hb'.le (by norm_num) a6
  have hbl : (j : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by gcongr
  have hS1 : L.Sc ≤ (D.R.k : ℝ) * L.Sc := le_mul_of_one_le_left hS.le (by linarith)
  rw [mul_div_assoc] at d4
  constructor <;> nlinarith

/- English proof (translation)
Introduce `u j hj z hz`. Take `⟨-, -, -, -, -, h4, h2b, -, -, -⟩` from `size_at Fm hx1 i hg`. Take `⟨e1, e2, e3, -⟩` from `top_rows_at Fm hx1 i u j hj z hz`. Take `⟨-, -, hw⟩` from `windows_at Fm hx1 i hg j hj z`. Take `⟨-, hw2⟩` from `hw hz`.

Generalize the expression as in `Fm.L x i = L at *`. Generalize the expression as in `Fm.D x i = D at *`. Establish `hxp : 0 < L.sc.x` using `by linarith`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `hb' : 0 < L.sc.b'` using `div_pos (mul_pos hxp hb) (Real.exp_pos _)`.

Establish `ha : aL L z.2 = L.aT ⟨z.2, hz.2⟩` using `by unfold aL; rw [dif_pos hz.2]`. Establish `hbb : bL L z.2 = L.bT ⟨z.2, hz.2⟩` using `by unfold bL; rw [dif_pos hz.2]`. Establish `a1` using `(L.aT_win ⟨z.2, hz.2⟩).1`. Establish `a2` using `L.bT_ge ⟨z.2, hz.2⟩`. Establish `a3 : 4 * L.sc.b ≤ L.sc.a`.

Unfold `Scale.a`. Conclude with `mul_le_mul_of_nonneg_right h4 hb.le`. Establish `hN : 0 < D.R.N j`. Use `D.R.m_add_three_le_k` as an intermediate fact. Unfold `Ranks.N`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[nuRowOK D u j hj z 0, if_pos hN, e1]`. Rewrite `e3` using `[e2, hbb]`. Rewrite using `[ha]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem two_w_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), IsTopPl (Fm.D x i) z → 2 * wPl (Fm.D x i) (j + 1) z ≤ (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ) := by
  intro u j hj z hz
  obtain ⟨-, -, -, -, -, h4, h2b, -, -, -⟩ := size_at Fm hx1 i hg
  obtain ⟨e1, e2, e3, -⟩ := top_rows_at Fm hx1 i u j hj z hz
  obtain ⟨-, -, hw⟩ := windows_at Fm hx1 i hg j hj z
  obtain ⟨-, hw2⟩ := hw hz
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hxp : 0 < L.sc.x := by linarith
  have hb : 0 < L.sc.b := Real.exp_pos _
  have hb' : 0 < L.sc.b' := div_pos (mul_pos hxp hb) (Real.exp_pos _)
  have ha : aL L z.2 = L.aT ⟨z.2, hz.2⟩ := by unfold aL; rw [dif_pos hz.2]
  have hbb : bL L z.2 = L.bT ⟨z.2, hz.2⟩ := by unfold bL; rw [dif_pos hz.2]
  have a1 := (L.aT_win ⟨z.2, hz.2⟩).1
  have a2 := L.bT_ge ⟨z.2, hz.2⟩
  have a3 : 4 * L.sc.b ≤ L.sc.a := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have hN : 0 < D.R.N j := by
    have := D.R.m_add_three_le_k
    unfold Ranks.N
    omega
  rw [nuRowOK D u j hj z 0, if_pos hN, e1]
  rw [e2, hbb] at e3
  rw [ha]
  linarith

/- English proof (translation)
Introduce `u j hj z`. Establish `hr` using `nuRow_le_at Fm (by linarith [hg.1]) hx1 i u (j + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (tauPl (Fm.D x i) z)`. Simplify using `only [Nat.add_sub_cancel] at hr`. Take `⟨hkN, -, -, -, -, h4, -, -, -, hS⟩` from `size_at Fm hx1 i hg`. Establish `hsx` using `Fm.L_x x i hx1`.

Rewrite using `[GlobalTheory.nuD_card_eq_sum_nuRow _ (nuRowOK _) u j hj z]`. Establish `hsum` using `Finset.sum_le_card_nsmul (Finset.range ((Fm.D x i).R.N j)) (fun r => DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r) (10 * x * (Fm.L x i).sc.b) (fun r hr' => (hr r (Finset.mem_range.1 hr')).2)`. Rewrite `hsum` using `[Finset.card_range, nsmul_eq_mul]`. Establish `hNle : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m`. Establish `: (Fm.D x i).R.N j ≤ (Fm.D x i).R.N (Fm.D x i).R.m`.

Unfold `Ranks.N`. Use `Nat.mul_le_mul_right ((Fm.D x i).R.t + 1) hj.le` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Establish `hk : (1 : ℝ) ≤ (Fm.D x i).R.k`.

Use `(Fm.D x i).R.m_add_three_le_k` as an intermediate fact. Conclude with `(by omega : 1 ≤ (Fm.D x i).R.k)` after adjusting the coercions. Establish `hN0 : (0 : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m` using `Nat.cast_nonneg _`. Establish `hNk` using `le_mul_of_one_le_left hN0 hk`. Establish `heta` using `(Fm.L x i).etaSz_pos`.

Establish `hb : 0 < (Fm.L x i).sc.b` using `Real.exp_pos _`. Establish `hN : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.L x i).sc.b / 10` using `by linarith`. Rewrite `h4` using `[hsx]`. Establish `hxb : 0 ≤ 10 * x * (Fm.L x i).sc.b` using `by positivity`. Establish `h5` using `mul_le_mul_of_nonneg_right hN hxb`.

Establish `ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b`. Unfold `Scale.a`. Rewrite using `[hsx]`. Rewrite using `[ha]`. Establish `h6 : x * (Fm.L x i).sc.b ^ 2 ≤ x * (x * (Fm.L x i).sc.b ^ 2)` using `le_mul_of_one_le_left (by positivity) (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem card_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (((nuD (Fm.D x i) u j z).card : ℕ) : ℝ) ≤ (Fm.L x i).sc.a ^ 2 := by
  intro u j hj z
  have hr := nuRow_le_at Fm (by linarith [hg.1]) hx1 i u (j + 1)
    (Finset.mem_Icc.2 ⟨by omega, by omega⟩) (tauPl (Fm.D x i) z)
  simp only [Nat.add_sub_cancel] at hr
  obtain ⟨hkN, -, -, -, -, h4, -, -, -, hS⟩ := size_at Fm hx1 i hg
  have hsx := Fm.L_x x i hx1
  rw [GlobalTheory.nuD_card_eq_sum_nuRow _ (nuRowOK _) u j hj z]
  have hsum := Finset.sum_le_card_nsmul (Finset.range ((Fm.D x i).R.N j))
    (fun r => DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r) (10 * x * (Fm.L x i).sc.b)
    (fun r hr' => (hr r (Finset.mem_range.1 hr')).2)
  rw [Finset.card_range, nsmul_eq_mul] at hsum
  have hNle : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
    have : (Fm.D x i).R.N j ≤ (Fm.D x i).R.N (Fm.D x i).R.m := by
      unfold Ranks.N
      have := Nat.mul_le_mul_right ((Fm.D x i).R.t + 1) hj.le
      omega
    exact_mod_cast this
  have hk : (1 : ℝ) ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    exact_mod_cast (by omega : 1 ≤ (Fm.D x i).R.k)
  have hN0 : (0 : ℝ) ≤ (Fm.D x i).R.N (Fm.D x i).R.m := Nat.cast_nonneg _
  have hNk := le_mul_of_one_le_left hN0 hk
  have heta := (Fm.L x i).etaSz_pos
  have hb : 0 < (Fm.L x i).sc.b := Real.exp_pos _
  have hN : ((Fm.D x i).R.N j : ℝ) ≤ (Fm.L x i).sc.b / 10 := by linarith
  rw [hsx] at h4
  have hxb : 0 ≤ 10 * x * (Fm.L x i).sc.b := by positivity
  have h5 := mul_le_mul_of_nonneg_right hN hxb
  have ha : (Fm.L x i).sc.a = x * (Fm.L x i).sc.b := by
    unfold Scale.a
    rw [hsx]
  rw [ha]
  have h6 : x * (Fm.L x i).sc.b ^ 2 ≤ x * (x * (Fm.L x i).sc.b ^ 2) :=
    le_mul_of_one_le_left (by positivity) (by linarith)
  nlinarith

/- English proof (translation)
Establish `hK` using `(Fm.sizes x hx1 i).2.2.1.1`. Establish `hsx` using `Fm.L_x x i hx1`. Establish `he` using `(Fm.L x i).sc.eps_pos`. Establish `he'` using `(Fm.L x i).sc.eps_lt`. Establish `hx0 : (0 : ℝ) < x` using `by linarith`.

Rewrite `hK` using `[hsx]`. Establish `h4 : x ^ (4 : ℕ) ≤ ((Fm.D x i).R.k : ℝ)`. Use `le_trans ?_ hK` and prove the remaining obligations. Rewrite using `[← Real.rpow_natCast]`. Apply `Real.rpow_le_rpow_of_exponent_le (by linarith)` to reduce the goal to its premises.

Unfold `szTh`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hL : (Fm.L x i).sc.L ≤ x`. Unfold `Scale.L`.

Rewrite using `[hsx]`. Combine the equalities or inequalities in the displayed calculation. Establish `hL0 : 0 ≤ (Fm.L x i).sc.L`. Unfold `Scale.L`. Rewrite using `[hsx]`.

Check the signs of the components of the expression. Establish `hla : Real.log (Fm.L x i).sc.a = Real.log x + (Fm.L x i).sc.L`. Unfold `Scale.a Scale.b`. Rewrite using `[hsx, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]`. Establish `hlx : Real.log x ≤ x` using `(Real.log_le_sub_one_of_pos hx0).trans (by linarith)`.

Establish `hlx0 : 0 ≤ Real.log x` using `Real.log_nonneg (by linarith)`. Establish `h5 : 1 ≤ Real.log 5`. Rewrite using `[Real.le_log_iff_exp_le (by norm_num)]`. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hb : Real.logb 5 ((Fm.L x i).sc.a ^ 2) ≤ 4 * x`. Rewrite using `[Real.logb, Real.log_pow, hla]`. Use `push_cast`. Use `(div_le_self (by linarith) h5).trans (by linarith)` and prove the remaining obligations. Establish `h27 : 27 ≤ x ^ 3`.

Combine the equalities or inequalities in the displayed calculation. Establish `: 27 * x ≤ x ^ 4`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rank_at (hx3 : 3 ≤ x) (hx1 : Fm.x1 < x) (i : Fm.Ix x) :
    2 * Real.logb 5 ((Fm.L x i).sc.a ^ 2) + 2 ≤ ((Fm.D x i).R.k : ℝ) - 1 := by
  have hK := (Fm.sizes x hx1 i).2.2.1.1
  have hsx := Fm.L_x x i hx1
  have he := (Fm.L x i).sc.eps_pos
  have he' := (Fm.L x i).sc.eps_lt
  have hx0 : (0 : ℝ) < x := by linarith
  rw [hsx] at hK
  have h4 : x ^ (4 : ℕ) ≤ ((Fm.D x i).R.k : ℝ) := by
    refine le_trans ?_ hK
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    unfold szTh
    push_cast
    linarith
  have hL : (Fm.L x i).sc.L ≤ x := by
    unfold Scale.L
    rw [hsx]
    calc x ^ (Fm.L x i).sc.eps ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ = x := Real.rpow_one x
  have hL0 : 0 ≤ (Fm.L x i).sc.L := by
    unfold Scale.L
    rw [hsx]
    positivity
  have hla : Real.log (Fm.L x i).sc.a = Real.log x + (Fm.L x i).sc.L := by
    unfold Scale.a Scale.b
    rw [hsx, Real.log_mul hx0.ne' (Real.exp_pos _).ne', Real.log_exp]
  have hlx : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h5 : 1 ≤ Real.log 5 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9
    linarith
  have hb : Real.logb 5 ((Fm.L x i).sc.a ^ 2) ≤ 4 * x := by
    rw [Real.logb, Real.log_pow, hla]
    push_cast
    refine (div_le_self (by linarith) h5).trans (by linarith)
  have h27 : 27 ≤ x ^ 3 := by
    calc (27 : ℝ) = 3 ^ 3 := by norm_num
      _ ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx3 3
  have : 27 * x ≤ x ^ 4 := by
    calc 27 * x ≤ x ^ 3 * x := mul_le_mul_of_nonneg_right h27 hx0.le
      _ = x ^ 4 := by ring
  linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, h4, -, -, hw, -⟩` from `size_at Fm hx1 i hg`. Establish `ha : 0 ≤ (Fm.L x i).sc.a`. Establish `h0 : 0 ≤ (Fm.L x i).sc.x` using `by linarith`. Unfold `Scale.a Scale.b`. Check the signs of the components of the expression.

Rewrite using `[Scale.X'']`. Conclude with `div_le_self ha hw`.
-/
theorem xa_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) :
    (Fm.L x i).sc.X'' (Fm.D x i).R.n ≤ (Fm.L x i).sc.a := by
  obtain ⟨-, -, -, -, -, h4, -, -, hw, -⟩ := size_at Fm hx1 i hg
  have ha : 0 ≤ (Fm.L x i).sc.a := by
    have h0 : 0 ≤ (Fm.L x i).sc.x := by linarith
    unfold Scale.a Scale.b
    positivity
  rw [Scale.X'']
  exact div_le_self ha hw

/- English proof (translation)
Introduce `u j hj z`. Take `⟨-, hw, -⟩` from `windows_at Fm hx1 i hg j hj z`. Establish `hr` using `long_at Fm hx1 i u j hj z`. Establish `hk : 5 ≤ (Fm.D x i).R.k`. Use `(Fm.D x i).R.m_add_three_le_k` as an intermediate fact.

Use `(Fm.D x i).R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hN : (Fm.D x i).R.k ≤ (Fm.D x i).R.N j` using `by unfold Ranks.N; omega`. Establish `hS` using `(Fm.L x i).Sc_pos`. Use `split_ifs with hz`.

Establish `e` using `nuRowOK (Fm.D x i) u j hj z 1`. Rewrite `e` using `[if_pos (by omega)]`. Use `((hr 1 (by omega)).2 hz le_rfl (by omega)).2` as an intermediate fact. Rewrite using `[e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `e` using `nuRowOK (Fm.D x i) u j hj z 0`. Rewrite `e` using `[if_pos (by omega)]`. Use `((hr 0 (by omega)).1 hz).2` as an intermediate fact. Rewrite `this` using `[if_pos rfl]`. Rewrite using `[e]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cap_width_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc := by
  intro u j hj z
  obtain ⟨-, hw, -⟩ := windows_at Fm hx1 i hg j hj z
  have hr := long_at Fm hx1 i u j hj z
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    have := (Fm.D x i).R.two_le_m
    omega
  have hN : (Fm.D x i).R.k ≤ (Fm.D x i).R.N j := by unfold Ranks.N; omega
  have hS := (Fm.L x i).Sc_pos
  split_ifs with hz
  · have e := nuRowOK (Fm.D x i) u j hj z 1
    rw [if_pos (by omega)] at e
    have := ((hr 1 (by omega)).2 hz le_rfl (by omega)).2
    rw [e]
    linarith
  · have e := nuRowOK (Fm.D x i) u j hj z 0
    rw [if_pos (by omega)] at e
    have := ((hr 0 (by omega)).1 hz).2
    rw [if_pos rfl] at this
    rw [e]
    linarith

/- English proof (translation)
Introduce `u j hj z`. Establish `hfill : fill (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z = wPl (Fm.D x i) (j + 1) z`. Take `⟨w⟩` from `GlobalTheory.nonempty_places_of_record (Fm.D x i)`. Use `(Fm.fills x hx i w).1 (j + 1) ?_ (tauPl _ z) z ?_` and prove the remaining obligations. Simplify using `only [SizeData₂.lifts, Finset.mem_Icc]`.

Use linear arithmetic over natural numbers and integers. Simplify using `[tauPl]`. Establish `hk : 5 ≤ (Fm.D x i).R.k`. Use `(Fm.D x i).R.m_add_three_le_k` as an intermediate fact. Use `(Fm.D x i).R.two_le_m` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hS` using `(Fm.L x i).Sc_pos`. Unfold `fillG cG`. Rewrite using `[hfill]`. Use `split_ifs with hz`.

Establish `h1` using `GlobalTheory.CapBound.row_le (Fm.D x i) u j hj z 1 le_rfl (by omega)`. Take `⟨-, h4⟩` from `(Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < _; omega)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h1` using `GlobalTheory.CapBound.row_le (Fm.D x i) u j hj z 0 (by omega) (by omega)`. Take `⟨-, h4⟩` from `GlobalTheory.LongRows.u_bounds_off (Fm.params x hx i) u _ (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) 0 (by omega)`.

Rewrite `h4` using `[if_pos rfl]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem cap_fill_at (hx : Fm.x1 < x) (i : Fm.Ix x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ fillG (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z + cG (Fm.L x i) := by
  intro u j hj z
  have hfill : fill (Fm.Gx x i) (bL (Fm.L x i)) (j + 1) z = wPl (Fm.D x i) (j + 1) z := by
    obtain ⟨w⟩ := GlobalTheory.nonempty_places_of_record (Fm.D x i)
    refine (Fm.fills x hx i w).1 (j + 1) ?_ (tauPl _ z) z ?_
    · simp only [SizeData₂.lifts, Finset.mem_Icc]; omega
    · simp [tauPl]
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k; have := (Fm.D x i).R.two_le_m; omega
  have hS := (Fm.L x i).Sc_pos
  unfold fillG cG
  rw [hfill]
  split_ifs with hz
  · have h1 := GlobalTheory.CapBound.row_le (Fm.D x i) u j hj z 1 le_rfl (by omega)
    obtain ⟨-, h4⟩ := (Fm.L x i).cloud_u u (tauPl (Fm.D x i) z) ⟨1, by omega⟩ le_rfl (by show 1 + 1 < _; omega)
    linarith
  · have h1 := GlobalTheory.CapBound.row_le (Fm.D x i) u j hj z 0 (by omega) (by omega)
    obtain ⟨-, h4⟩ := GlobalTheory.LongRows.u_bounds_off (Fm.params x hx i) u _
      (GlobalTheory.LongRows.not_mem_topPlaces _ z hz) 0 (by omega)
    rw [if_pos rfl] at h4
    linarith

/- English proof (translation)
Introduce `u j hj t ht`. Take `⟨s1, -, -, -, -, h4, -, -, -, s2⟩` from `size_at Fm hx1 i hg`. Establish `hz : IsTopPl (Fm.D x i) (false, t)` using `⟨rfl, ht⟩`. Establish `hk : 5 ≤ (Fm.D x i).R.k`. Use `(Fm.D x i).R.m_add_three_le_k` as an intermediate fact.

Use `(Fm.D x i).R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨r1, -⟩` from `(long_at Fm hx1 i u j hj (false, t) 1 (by omega)).2 hz le_rfl (by omega)`. Take `⟨e1, -⟩` from `GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj (false, t) hz`. Generalize the expression as in `Fm.L x i = L at *`.

Generalize the expression as in `Fm.D x i = D at *`. Establish `hN : D.R.k ≤ D.R.N j` using `by unfold Ranks.N; omega`. Establish `hk' : (5 : ℝ) ≤ D.R.k` using `by exact_mod_cast hk`. Establish `hb : 0 < L.sc.b` using `Real.exp_pos _`. Establish `ha : aL L t = L.aT ⟨t, ht⟩` using `by unfold aL; rw [dif_pos ht]`.

Establish `a1` using `(L.aT_win ⟨t, ht⟩).2`. Establish `a3 : 4 * L.sc.b ≤ L.sc.a`. Unfold `Scale.a`. Conclude with `mul_le_mul_of_nonneg_right h4 hb.le`. Establish `hp : 1 ≤ L.sc.x ^ (Scale.A / 2)` using `Real.one_le_rpow (by linarith) (by unfold Scale.A; norm_num)`.

Establish `a4 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5` using `div_le_div_of_nonneg_left (by linarith) (by norm_num) (by nlinarith)`. Establish `hka : 0 ≤ kaJ D (j + 1)`. Unfold `kaJ`. Use `push_cast`. Establish `: (0 : ℝ) ≤ (2 * ((j : ℝ) + 1) - 1)` using `by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith`.

Check the signs of the components of the expression. Establish `hNm : (D.R.N D.R.m : ℝ) ≤ (D.R.k : ℝ) * D.R.N D.R.m` using `le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith)`. Establish `he` using `L.etaSz_pos`. Rewrite using `[nuRowOK D u j hj, nuRowOK D u j hj, if_pos (by omega), if_pos (by omega), e1]`. Simplify using `only [ha]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem gap_at (hx1 : Fm.x1 < x) (i : Fm.Ix x) (hg : Big eps x) : ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ t ∈ (Fm.D x i).host.TT, (((nuD (Fm.D x i) u j (false, t)).rowLen 0 : ℕ) : ℝ) - (((nuD (Fm.D x i) u j (false, t)).rowLen 1 : ℕ) : ℝ) ≤ 2 * (Fm.L x i).sc.a := by
  intro u j hj t ht
  obtain ⟨s1, -, -, -, -, h4, -, -, -, s2⟩ := size_at Fm hx1 i hg
  have hz : IsTopPl (Fm.D x i) (false, t) := ⟨rfl, ht⟩
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    have := (Fm.D x i).R.two_le_m
    omega
  obtain ⟨r1, -⟩ := (long_at Fm hx1 i u j hj (false, t) 1 (by omega)).2 hz le_rfl (by omega)
  obtain ⟨e1, -⟩ := GlobalTheory.TopRows.nuRow_tauPl_of_isTopPl (Fm.L x i) u j hj (false, t) hz
  generalize Fm.L x i = L at *
  generalize Fm.D x i = D at *
  have hN : D.R.k ≤ D.R.N j := by unfold Ranks.N; omega
  have hk' : (5 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hb : 0 < L.sc.b := Real.exp_pos _
  have ha : aL L t = L.aT ⟨t, ht⟩ := by unfold aL; rw [dif_pos ht]
  have a1 := (L.aT_win ⟨t, ht⟩).2
  have a3 : 4 * L.sc.b ≤ L.sc.a := by
    unfold Scale.a
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have hp : 1 ≤ L.sc.x ^ (Scale.A / 2) :=
    Real.one_le_rpow (by linarith) (by unfold Scale.A; norm_num)
  have a4 : L.sc.a / ((D.R.k : ℝ) * L.sc.x ^ (Scale.A / 2)) ≤ L.sc.a / 5 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) (by nlinarith)
  have hka : 0 ≤ kaJ D (j + 1) := by
    unfold kaJ
    push_cast
    have : (0 : ℝ) ≤ (2 * ((j : ℝ) + 1) - 1) := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith
    positivity
  have hNm : (D.R.N D.R.m : ℝ) ≤ (D.R.k : ℝ) * D.R.N D.R.m :=
    le_mul_of_one_le_left (Nat.cast_nonneg _) (by linarith)
  have he := L.etaSz_pos
  rw [nuRowOK D u j hj, nuRowOK D u j hj, if_pos (by omega), if_pos (by omega), e1]
  simp only [ha]
  linarith

/- English proof (translation)
Establish `h11` using `Formalism.MainNotions.SizesAt.eleven_le (Fm.sizes x h1 i)`. Use linear arithmetic over natural numbers and integers.
-/
theorem three_le_split_at (h0 : 0 < eps) (hx : (3 : ℝ) ^ (5 / eps) ≤ x) (h1 : Fm.x1 < x)
    (i : Fm.Ix x) : 3 ≤ (Fm.D x i).host.splitBound := by
  have h11 := Formalism.MainNotions.SizesAt.eleven_le (Fm.sizes x h1 i)
  omega

/- English proof (translation)
Introduce `eps`. Distinguish the cases in `he : 0 < eps`. Take `⟨x0, hx0⟩` from `GlobalTheory.ShNums.pow_six_le_exp he`. Use `⟨max x0 ((3 : ℝ) ^ (5 / eps)), fun Fm x hx hx1 i Ee => ?_⟩` and prove the remaining obligations. Establish `hg : Big eps x` using `hx0 x (le_trans (le_max_left _ _) hx)`.

Establish `h3 : (3 : ℝ) ^ (5 / eps) ≤ x` using `le_trans (le_max_right _ _) hx`. Establish `hx3 : (3 : ℝ) ≤ x` using `by linarith [hg.1]`. Use `⟨?_, fun u j hj t ht => ?_, three_le_split_at Fm he h3 hx1 i⟩` and prove the remaining obligations. Conclude with `{ wpos := fun j hj z => by`. Establish `h2` using `(windows_at Fm hx1 i hg j hj z).1`.

Take `⟨-, -, -, -, -, -, -, -, hw, -⟩` from `size_at Fm hx1 i hg`. Combine the linear equalities and inequalities to obtain the conclusion. Use `low := fun u j hj z hz => by`. Rewrite using `[GlobalTheory.ShapeRows.ent_size Ee u j hj z]`. Conclude with `excess_at Fm hx1 i hg u j hj z hz`.

Use `top := fun u j hj z hz => by`. Rewrite using `[GlobalTheory.ShapeRows.ent_size Ee u j hj z, GlobalTheory.ShapeRows.ent_row Ee u j hj z]`. Conclude with `top_excess_at Fm hx1 i hg u j hj z hz`. Use `top1 := fun u j hj z hz => by`. Rewrite using `[GlobalTheory.ShapeRows.ent_row Ee u j hj z]`.

Conclude with `two_w_at Fm hx1 i hg u j hj z hz`. Use `sizeA := fun u j hj z => by`. Rewrite using `[GlobalTheory.ShapeRows.ent_size Ee u j hj z]`. Conclude with `card_at Fm hx1 i hg u j hj z`. Use `rankA := rank_at Fm hx3 hx1 i`.

Use `xa := ⟨xa_at Fm hx1 i hg, GlobalTheory.scale_one_lt_a _⟩`. Use `capW := fun u j hj z => by`. Rewrite using `[GlobalTheory.ShapeRows.ent_cap Ee u j hj z]`. Conclude with `cap_width_at Fm hx1 i hg u j hj z`. Use `alG := fun u j hj t ht => by`.

Rewrite using `[GlobalTheory.ShapeRows.ent_row Ee u j hj, GlobalTheory.ShapeRows.ent_row Ee u j hj]`. Conclude with `GlobalTheory.AlTop.al_le_rowLen_sub (Fm.L x i) u j hj t ht`. Use `capG := fun u j hj z => by`. Rewrite using `[GlobalTheory.ShapeRows.ent_cap Ee u j hj z]`. Conclude with `cap_fill_at Fm hx1 i u j hj z }`.

Rewrite using `[GlobalTheory.ShapeRows.ent_row Ee u j hj, GlobalTheory.ShapeRows.ent_row Ee u j hj]`. Conclude with `gap_at Fm hx1 i hg u j hj t ht`. Use `⟨0, fun Fm x _ _ i Ee => absurd ?_ he⟩` and prove the remaining obligations. Take `⟨i0⟩` from `Fm.Ix_zero`. Rewrite using `[← Fm.L_eps 0 i0]`.

Conclude with `(Fm.L 0 i0).sc.eps_pos`.
-/
theorem shape_uniform : ∀ eps : ℝ, ∃ x0 : ℝ, ∀ (Fm : FamP eps), ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (Ee : OrbitPlaces.Ent (Fm.D x i)), OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Ee ∧ (∀ u, ∀ j < (Fm.D x i).R.m, ∀ t ∈ (Fm.D x i).host.TT, Ee.row u j (false, t) 0 - Ee.row u j (false, t) 1 ≤ 2 * (Fm.L x i).sc.a) ∧ 3 ≤ (Fm.D x i).host.splitBound := by
  intro eps
  by_cases he : 0 < eps
  · obtain ⟨x0, hx0⟩ := GlobalTheory.ShNums.pow_six_le_exp he
    refine ⟨max x0 ((3 : ℝ) ^ (5 / eps)), fun Fm x hx hx1 i Ee => ?_⟩
    have hg : Big eps x := hx0 x (le_trans (le_max_left _ _) hx)
    have h3 : (3 : ℝ) ^ (5 / eps) ≤ x := le_trans (le_max_right _ _) hx
    have hx3 : (3 : ℝ) ≤ x := by linarith [hg.1]
    refine ⟨?_, fun u j hj t ht => ?_, three_le_split_at Fm he h3 hx1 i⟩
    · exact
        { wpos := fun j hj z => by
            have h2 := (windows_at Fm hx1 i hg j hj z).1
            obtain ⟨-, -, -, -, -, -, -, -, hw, -⟩ := size_at Fm hx1 i hg
            linarith
          low := fun u j hj z hz => by
            rw [GlobalTheory.ShapeRows.ent_size Ee u j hj z]
            exact excess_at Fm hx1 i hg u j hj z hz
          top := fun u j hj z hz => by
            rw [GlobalTheory.ShapeRows.ent_size Ee u j hj z, GlobalTheory.ShapeRows.ent_row Ee u j hj z]
            exact top_excess_at Fm hx1 i hg u j hj z hz
          top1 := fun u j hj z hz => by
            rw [GlobalTheory.ShapeRows.ent_row Ee u j hj z]
            exact two_w_at Fm hx1 i hg u j hj z hz
          sizeA := fun u j hj z => by
            rw [GlobalTheory.ShapeRows.ent_size Ee u j hj z]
            exact card_at Fm hx1 i hg u j hj z
          rankA := rank_at Fm hx3 hx1 i
          xa := ⟨xa_at Fm hx1 i hg, GlobalTheory.scale_one_lt_a _⟩
          capW := fun u j hj z => by
            rw [GlobalTheory.ShapeRows.ent_cap Ee u j hj z]
            exact cap_width_at Fm hx1 i hg u j hj z
          alG := fun u j hj t ht => by
            rw [GlobalTheory.ShapeRows.ent_row Ee u j hj, GlobalTheory.ShapeRows.ent_row Ee u j hj]
            exact GlobalTheory.AlTop.al_le_rowLen_sub (Fm.L x i) u j hj t ht
          capG := fun u j hj z => by
            rw [GlobalTheory.ShapeRows.ent_cap Ee u j hj z]
            exact cap_fill_at Fm hx1 i u j hj z }
    · rw [GlobalTheory.ShapeRows.ent_row Ee u j hj, GlobalTheory.ShapeRows.ent_row Ee u j hj]
      exact gap_at Fm hx1 i hg u j hj t ht
  · refine ⟨0, fun Fm x _ _ i Ee => absurd ?_ he⟩
    obtain ⟨i0⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i0]
    exact (Fm.L 0 i0).sc.eps_pos

end GlobalTheory.ShapeUniform
