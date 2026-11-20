import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.SlopeExcess.FamilyStatementOfScaledLemmas
import Formalism.SharpRestriction.Divisibility.SlopeExcess.ConstRankBaseLePolyFourth

noncomputable section

namespace Formalism.MainNotions.DIV.Proofs

open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions

/- English proof (translation)
Establish `hRpos : (0 : ℝ) < (Rsum D.div.Nu : ℝ)`. Establish `h0 : 0 < Rsum D.div.Nu`. Unfold `Rsum`. Conclude with `lt_of_lt_of_le (hr D.u₀) (Finset.single_le_sum (f := fun u => dU D.div.Nu u) (fun _ _ => Nat.zero_le _) (Finset.mem_univ D.u₀))`. Conclude with `h0` after adjusting the coercions.

Establish `hsum : (∑ u, (dU D.div.Nu u : ℝ) * ((D.div.Nu u).mu - hExpl6 D L Z Csz u)) ≤ (∑ u, (dU D.div.Nu u : ℝ)) * (L.sc.x ^ CH * L.sc.b - D.div.RR.muMax)`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (by linarith [h u]) (Nat.cast_nonneg _)`. Establish `hR : (∑ u, (dU D.div.Nu u : ℝ)) = (Rsum D.div.Nu : ℝ)`. Unfold `Rsum`.

Use `push_cast`. Both sides reduce to the same expression. Establish `hs : sFrame D.div.Nu (hExpl6 D L Z Csz) ≤ L.sc.x ^ CH * L.sc.b - D.div.RR.muMax`. Unfold `sFrame`. Rewrite using `[div_le_iff₀ hRpos]`.

Rewrite `hsum` using `[hR]`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `Formalism.MainNotions.LocalQuadraticParts.FrameNumberBound Formalism.MainNotions.LocalQuadraticParts.sExpl`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem height_bound_of_word_slopes (D : D7) (L : SizeData₂ D) (Z : DivX D) (Csz CH : ℝ)
    (hr : ∀ u, 0 < (D.div.Nu u).rank)
    (h : ∀ u, (D.div.Nu u).mu - hExpl6 D L Z Csz u + D.div.RR.muMax ≤ L.sc.x ^ CH * L.sc.b) :
    Formalism.MainNotions.LocalQuadraticParts.FrameNumberBound D L Z Csz CH := by
  classical
  have hRpos : (0 : ℝ) < (Rsum D.div.Nu : ℝ) := by
    have h0 : 0 < Rsum D.div.Nu := by
      unfold Rsum
      exact lt_of_lt_of_le (hr D.u₀)
        (Finset.single_le_sum (f := fun u => dU D.div.Nu u) (fun _ _ => Nat.zero_le _) (Finset.mem_univ D.u₀))
    exact_mod_cast h0
  have hsum : (∑ u, (dU D.div.Nu u : ℝ) * ((D.div.Nu u).mu - hExpl6 D L Z Csz u)) ≤
      (∑ u, (dU D.div.Nu u : ℝ)) * (L.sc.x ^ CH * L.sc.b - D.div.RR.muMax) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun u _ =>
      mul_le_mul_of_nonneg_left (by linarith [h u]) (Nat.cast_nonneg _)
  have hR : (∑ u, (dU D.div.Nu u : ℝ)) = (Rsum D.div.Nu : ℝ) := by
    unfold Rsum; push_cast; rfl
  have hs : sFrame D.div.Nu (hExpl6 D L Z Csz) ≤ L.sc.x ^ CH * L.sc.b - D.div.RR.muMax := by
    unfold sFrame
    rw [div_le_iff₀ hRpos]
    rw [hR] at hsum
    linarith
  unfold Formalism.MainNotions.LocalQuadraticParts.FrameNumberBound Formalism.MainNotions.LocalQuadraticParts.sExpl
  linarith

def HHRestB {eps : ℝ} (Fm : FamP eps) (CH : ℝ) : Prop :=
  ∀ C : ℝ, ∃ x0 : ℝ, ∀ x, x0 ≤ x → Fm.x1 < x → ∀ (i : Fm.Ix x) u,
    (((Fm.D x i).fm u).lat 0).muMax + (Fm.L x i).Ga + (Fm.L x i).Fo - (Fm.L x i).Ee u +
      C * (Fm.D x i).R.m * (Fm.L x i).B0 - hExpl6 (Fm.D x i) (Fm.L x i) (Fm.X x i) Fm.Csz u +
      (Fm.D x i).div.RR.muMax ≤ (Fm.L x i).sc.x ^ CH * (Fm.L x i).sc.b

/- English proof (translation)
Take `⟨C, x4, h4⟩` from `h4`. Take `⟨xr, hrk⟩` from `hrk`. Take `⟨xf, hfull⟩` from `hfull`. Take `⟨xs, hrest⟩` from `hrest C`. Use `⟨max (max x4 xr) (max xf xs), fun x hx hx1 i => ?_⟩` and prove the remaining obligations.

Establish `g4 : x4 ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `gr : xr ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `gf : xf ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Establish `gs : xs ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Establish `hp` using `h4 x g4 i (Formalism.MainNotions.LocalQuadraticParts.defs_fam Fm hx1 i)`.

Use `height_bound_of_word_slopes _ _ _ _ _ (hrk x gr i) fun u => ?_` and prove the remaining obligations. Establish `hmu : ((Fm.D x i).div.Nu u).mu ≤ ((Fm.D x i).div.Nu u).muMax`. Establish `hne : ((Fm.D x i).div.Nu u).L ≠ ⊥`. Introduce `h0`. Establish `hpos` using `hrk x gr i u`.

Unfold `HLat.rank Formalism.HN.rkK at hpos`. Establish `hb : Submodule.span (Fm.D x i).what₂.LL (((Fm.D x i).div.Nu u).L : Set ((Fm.D x i).div.Nu u).V) = ⊥` using `Submodule.span_eq_bot.mpr fun y hy => by`. Rewrite `hy` using `[h0]`. Conclude with `(Submodule.mem_bot _).1 hy`. Rewrite `hpos` using `[hb, finrank_bot]`.

Conclude with `lt_irrefl 0 hpos`. Conclude with `Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms.mu_le_muMax _ _ ((Fm.D x i).div_good.2 u) _ (hfull x gf i u).1 hne`. Combine the linear relations using `[(hp u).1, hrest x gs hx1 i u]`.
-/
theorem height_bound_of_slope_fullness {eps : ℝ} (Fm : FamP eps) (CH : ℝ) (h4 : Formalism.MainNotions.LocalQuadraticParts.SlopeLemmaFamily Fm)
    (hrk : Formalism.MainNotions.J.MuRank Fm) (hfull : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).NuFull)
    (hrest : HHRestB Fm CH) : Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH := by
  obtain ⟨C, x4, h4⟩ := h4
  obtain ⟨xr, hrk⟩ := hrk
  obtain ⟨xf, hfull⟩ := hfull
  obtain ⟨xs, hrest⟩ := hrest C
  refine ⟨max (max x4 xr) (max xf xs), fun x hx hx1 i => ?_⟩
  have g4 : x4 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have gr : xr ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have gf : xf ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have gs : xs ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hp := h4 x g4 i (Formalism.MainNotions.LocalQuadraticParts.defs_fam Fm hx1 i)
  refine height_bound_of_word_slopes _ _ _ _ _ (hrk x gr i) fun u => ?_
  have hmu : ((Fm.D x i).div.Nu u).mu ≤ ((Fm.D x i).div.Nu u).muMax := by
    have hne : ((Fm.D x i).div.Nu u).L ≠ ⊥ := by
      intro h0
      have hpos := hrk x gr i u
      unfold HLat.rank Formalism.HN.rkK at hpos
      have hb : Submodule.span (Fm.D x i).what₂.LL (((Fm.D x i).div.Nu u).L : Set ((Fm.D x i).div.Nu u).V) = ⊥ :=
        Submodule.span_eq_bot.mpr fun y hy => by
          rw [h0] at hy
          exact (Submodule.mem_bot _).1 hy
      rw [hb, finrank_bot] at hpos
      exact lt_irrefl 0 hpos
    exact Formalism.MainNotions.DIV.Proofs.ScaledLatticeNorms.mu_le_muMax _ _ ((Fm.D x i).div_good.2 u) _ (hfull x gf i u).1 hne
  linarith [(hp u).1, hrest x gs hx1 i u]

def EdHH (l : List ℝ) : ℝ := 9 * (max (l.headD 0) 5 + 3) + 1

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cOut_headD {eps : ℝ} (Fm : FamP eps) : Fm.cOut.headD 0 = Fm.Ct := rfl

def thrHH (Eb Ec CF0 : List ℝ → ℝ) : TransportedAlt :=
  ⟨0, fun _ => 0, fun l => max (max (Eb l) (Ec l)) (max (CF0 l) (EdHH l)) + 1, fun _ => 0⟩

/- English proof (translation)
Introduce `C`. Take `⟨xb, hb⟩` from `hb`. Take `⟨xc, hc⟩` from `hc`. Take `⟨xd, hd⟩` from `hExpl6_lower_pow Fm hTu`. Take `⟨xe, he⟩` from `he`.

Use `⟨max (max xb xc) (max xd (max xe (max 9 |C|))), fun x hx hx1 i u => ?_⟩` and prove the remaining obligations. Establish `gb : xb ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx`. Establish `gc : xc ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx`. Establish `gd : xd ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Establish `ge : xe ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx`.

Establish `g9 : max 9 |C| ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx`. Establish `hsc : (Fm.L x i).sc.x = x` using `Fm.L_x x i hx1`. Establish `hCt : (Fm.L x i).Ct = Fm.Ct` using `Fm.Ct_eq x i`. Establish `hx9 : 9 ≤ x` using `(le_max_left _ _).trans g9`. Establish `hx0 : 0 < x` using `by linarith`.

Establish `hx1' : 1 ≤ x` using `by linarith`. Establish `tb` using `hb x gb hx1 i u`. Establish `tc` using `hc x gc hx1 i u`. Establish `td` using `hd x gd hx1 i u`. Establish `te` using `he x ge hx1 i`.

Establish `t0` using `(const_rank_base_le_poly_fourth (L := Fm.L x i) C).trans (bPol_le (Fm.sizes x hx1 i) |C| 4 (by rw [hsc]; exact g9))`. Rewrite `tb`, `tc`, `te`, `t0`, the goal using `[hsc]`. Rewrite `t0` using `[hCt]`. Use `set b := (Fm.L x i).sc.b`. Establish `hb1 : 1 ≤ b` using `HHParts.one_le_b (Fm.L x i)`.

Use `set E := max (max (Eb Fm.cOut) (Ec Fm.cOut)) (max (CF0 Fm.cOut) (EdHH Fm.cOut)) with hE`. Establish `rp : ∀ a : ℝ, a ≤ E → x ^ a * b ≤ x ^ E * b` using `fun a h => mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1' h) (by linarith)`. Establish `hEd : EdHH Fm.cOut = 9 * (max Fm.Ct 5 + 3) + 1` using `by unfold EdHH; rw [cOut_headD]`. Establish `u1` using `rp _ (le_trans (le_max_left _ _) (le_max_left _ _) : Eb Fm.cOut ≤ E)`. Establish `u2` using `rp _ (le_trans (le_max_right _ _) (le_max_left _ _) : Ec Fm.cOut ≤ E)`.

Establish `u3` using `rp _ (le_trans (le_max_left _ _) (le_max_right _ _) : CF0 Fm.cOut ≤ E)`. Establish `hdE : 9 * (max Fm.Ct 5 + 3) + 1 ≤ E` using `hEd ▸ le_trans (le_max_right _ _) (le_max_right _ _)`. Establish `u4` using `rp _ hdE`. Establish `h5 : (0:ℝ) ≤ max Fm.Ct 5 + 3` using `by have := le_max_right Fm.Ct 5; linarith`. Establish `u5` using `rp (((4 : ℕ) : ℝ) * (max Fm.Ct 5 + 3) + 1) (by push_cast; linarith)`.

Establish `hxE : x ^ (E + 1) * b = x * (x ^ E * b)` using `by rw [Real.rpow_add hx0, Real.rpow_one]; ring`. Establish `hCHb : x ^ (E + 1) * b ≤ x ^ CH * b` using `mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1' hCH) (by linarith)`. Establish `hpos : 0 ≤ x ^ E * b` using `by positivity`. Establish `h5x : 5 * (x ^ E * b) ≤ x * (x ^ E * b)` using `mul_le_mul_of_nonneg_right (by linarith) hpos`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hhRest_of_parts {eps : ℝ} (Fm : FamP eps) (CH : ℝ) (Eb Ec CF0 : List ℝ → ℝ)
    (hCH : max (max (Eb Fm.cOut) (Ec Fm.cOut)) (max (CF0 Fm.cOut) (EdHH Fm.cOut)) + 1 ≤ CH)
    (hb : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (((Fm.D x i).fm u).lat 0).muMax ≤ (Fm.L x i).sc.x ^ Eb Fm.cOut * (Fm.L x i).sc.b)
    (hc : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (Fm.L x i).Ga + (Fm.L x i).Fo - (Fm.L x i).Ee u ≤ (Fm.L x i).sc.x ^ Ec Fm.cOut * (Fm.L x i).sc.b)
    (hTu : TuSize Fm)
    (he : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b) :
    HHRestB Fm CH := by
  intro C
  obtain ⟨xb, hb⟩ := hb
  obtain ⟨xc, hc⟩ := hc
  obtain ⟨xd, hd⟩ := hExpl6_lower_pow Fm hTu
  obtain ⟨xe, he⟩ := he
  refine ⟨max (max xb xc) (max xd (max xe (max 9 |C|))), fun x hx hx1 i u => ?_⟩
  have gb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have gc : xc ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have gd : xd ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have ge : xe ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have g9 : max 9 |C| ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have hsc : (Fm.L x i).sc.x = x := Fm.L_x x i hx1
  have hCt : (Fm.L x i).Ct = Fm.Ct := Fm.Ct_eq x i
  have hx9 : 9 ≤ x := (le_max_left _ _).trans g9
  have hx0 : 0 < x := by linarith
  have hx1' : 1 ≤ x := by linarith
  have tb := hb x gb hx1 i u
  have tc := hc x gc hx1 i u
  have td := hd x gd hx1 i u
  have te := he x ge hx1 i
  have t0 := (const_rank_base_le_poly_fourth (L := Fm.L x i) C).trans
    (bPol_le (Fm.sizes x hx1 i) |C| 4 (by rw [hsc]; exact g9))
  rw [hsc] at tb tc te t0 ⊢
  rw [hCt] at t0
  set b := (Fm.L x i).sc.b
  have hb1 : 1 ≤ b := HHParts.one_le_b (Fm.L x i)
  set E := max (max (Eb Fm.cOut) (Ec Fm.cOut)) (max (CF0 Fm.cOut) (EdHH Fm.cOut)) with hE
  have rp : ∀ a : ℝ, a ≤ E → x ^ a * b ≤ x ^ E * b := fun a h =>
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1' h) (by linarith)
  have hEd : EdHH Fm.cOut = 9 * (max Fm.Ct 5 + 3) + 1 := by unfold EdHH; rw [cOut_headD]
  have u1 := rp _ (le_trans (le_max_left _ _) (le_max_left _ _) : Eb Fm.cOut ≤ E)
  have u2 := rp _ (le_trans (le_max_right _ _) (le_max_left _ _) : Ec Fm.cOut ≤ E)
  have u3 := rp _ (le_trans (le_max_left _ _) (le_max_right _ _) : CF0 Fm.cOut ≤ E)
  have hdE : 9 * (max Fm.Ct 5 + 3) + 1 ≤ E := hEd ▸ le_trans (le_max_right _ _) (le_max_right _ _)
  have u4 := rp _ hdE
  have h5 : (0:ℝ) ≤ max Fm.Ct 5 + 3 := by have := le_max_right Fm.Ct 5; linarith
  have u5 := rp (((4 : ℕ) : ℝ) * (max Fm.Ct 5 + 3) + 1) (by push_cast; linarith)
  have hxE : x ^ (E + 1) * b = x * (x ^ E * b) := by rw [Real.rpow_add hx0, Real.rpow_one]; ring
  have hCHb : x ^ (E + 1) * b ≤ x ^ CH * b :=
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hx1' hCH) (by linarith)
  have hpos : 0 ≤ x ^ E * b := by positivity
  have h5x : 5 * (x ^ E * b) ≤ x * (x ^ E * b) := mul_le_mul_of_nonneg_right (by linarith) hpos
  linarith

/- English proof (translation)
The claim follows from `height_bound_of_slope_fullness Fm CH h4 hrk hfull (hhRest_of_parts Fm CH Eb Ec CF0 (hL.2.2.1 CH List.mem_cons_self) hb hc hTu he)`.
-/
theorem height_bound_of_component_bounds {eps : ℝ} (Fm : FamP eps) (CH : ℝ) (Eb Ec CF0 : List ℝ → ℝ)
    (hL : Fm.Large (thrHH Eb Ec CF0) CH)
    (h4 : Formalism.MainNotions.LocalQuadraticParts.SlopeLemmaFamily Fm) (hrk : Formalism.MainNotions.J.MuRank Fm)
    (hfull : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, (Fm.D x i).NuFull)
    (hb : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (((Fm.D x i).fm u).lat 0).muMax ≤ (Fm.L x i).sc.x ^ Eb Fm.cOut * (Fm.L x i).sc.b)
    (hc : ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) u,
      (Fm.L x i).Ga + (Fm.L x i).Fo - (Fm.L x i).Ee u ≤ (Fm.L x i).sc.x ^ Ec Fm.cOut * (Fm.L x i).sc.b)
    (hTu : TuSize Fm)
    (he : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (_ : Fm.x1 < x) (i : Fm.Ix x),
      (Fm.D x i).div.RR.muMax + meanE (Fm.D x i) (fun e => Real.log ((Fm.X x i).kapR e)) ≤
        (Fm.L x i).sc.x ^ CF0 Fm.cOut * (Fm.L x i).sc.b) :
    Formalism.MainNotions.LocalQuadraticParts.FrameNumberBoundFamily Fm Fm.Csz CH :=
  height_bound_of_slope_fullness Fm CH h4 hrk hfull
    (hhRest_of_parts Fm CH Eb Ec CF0 (hL.2.2.1 CH List.mem_cons_self) hb hc hTu he)

end Formalism.MainNotions.DIV.Proofs

end
