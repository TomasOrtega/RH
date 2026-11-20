import Mathlib
import Formalism.SharpRestriction.Divisibility.FlipOneTwo
import Formalism.DegreeFormula.PointDegree.FlagDeg
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ArithmeticCylinders
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.GelfandTransference.HadamardGelfand.Transference

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions

structure JetSit (D : D7) (P : ModuliIntegralCharts.Prov D) (l q DF : ℕ) where
  w : P.Dat
  y : (P.loc w l).Pt (P.loc w l).Xm
  nW : ℕ
  hq : ModuliIntegralCharts.NHyp D l q
  hDF : 3 * DF + 2 ≤ q
  sg : (P.loc w l).At y ((P.loc w l).latStd nW) q → (P.loc w l).Th y ((P.loc w l).latStd nW) q
  hsg : (P.loc w l).SymLift y ((P.loc w l).latStd nW) q sg
  ev : (P.loc w l).Jet y ((P.loc w l).latStd nW) q DF →ₗ[((P.loc w l).fld y).C] ((P.loc w l).fld y).C

namespace JetSit

variable {D : D7} {P : ModuliIntegralCharts.Prov D} {l q DF : ℕ} (S : JetSit D P l q DF)

def thetaNorms : Set ℝ :=
  Set.range fun x => ‖S.ev ((P.loc S.w l).jet S.y ((P.loc S.w l).latStd S.nW) q DF
    ((P.loc S.w l).act S.y ((P.loc S.w l).latStd S.nW) q (S.sg x)
      ((P.loc S.w l).vth S.y ((P.loc S.w l).latStd S.nW) q)))‖

def germNorms : Set ℝ :=
  (fun v => ‖S.ev v‖) '' ((P.loc S.w l).intJet S.y ((P.loc S.w l).latStd S.nW) q DF : Set _)

/- English proof (translation)
Take `⟨_, H⟩` from `h S.w l hl q DF S.nW S.hq S.hDF S.y`. Take `⟨t, ht, hv⟩` from `H S.sg S.hsg`. Establish `hl1 : (1 : ℝ) < l` using `by exact_mod_cast hl.one_lt`. Establish `hl0 : (0 : ℝ) < l` using `by linarith`. Establish `htpos : 0 < ‖t‖` using `lt_of_lt_of_le (Real.rpow_pos_of_pos hl0 _) ht`.

Establish `key : ∀ u ∈ ModuliIntegralCharts.Ospan (C` using `((P.loc S.w l).fld S.y).C) ((P.loc S.w l).secJet S.y ((P.loc S.w l).latStd S.nW) q DF S.sg), ‖S.ev u‖ ≤ (l : ℝ) ^ (-a) := by`. Introduce `u hu`. Unfold `ModuliIntegralCharts.Ospan at hu`. Proceed by induction on `hu using AddSubgroup.closure_induction with`. Consider the case `mem u hu`.

Take `⟨α, hα, s, ⟨x, rfl⟩, rfl⟩` from `hu`. Rewrite using `[map_smul, smul_eq_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `zero => rw [map_zero, norm_zero]`. Conclude with `(Real.rpow_pos_of_pos hl0 _).le`.

Consider the case `add u v _ _ hu hv`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)`. Consider the case `neg u _ hu => rwa [map_neg, norm_neg]`. Establish `ub : (l : ℝ) ^ (-b) ≤ (l : ℝ) ^ (-a) / ‖t‖` using `hb.2 (by`.

Introduce and unpack `_ ⟨v, hv', rfl⟩`. Rewrite using `[le_div_iff₀ htpos]`. Use `key _ (hv v hv')` as an intermediate fact. Rewrite using `[map_smul, smul_eq_mul, norm_mul, mul_comm] at this)` and apply the resulting hypothesis. Establish `h2 : (l : ℝ) ^ (-b) ≤ (l : ℝ) ^ (-a + (P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y)`.

Use `ub.trans ?_` and prove the remaining obligations. Rewrite using `[div_le_iff₀ htpos, Real.rpow_add hl0, mul_assoc]`. Establish `h3 : 1 ≤ (l : ℝ) ^ ((P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y) * ‖t‖`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Real.rpow_add hl0]`.

Simplify using the standard rewrite rules. Use `_ ≤ _ := mul_le_mul_of_nonneg_left ht (Real.rpow_pos_of_pos hl0 _).le`. Combine the equalities or inequalities in the displayed calculation. Establish `h4` using `(Real.rpow_le_rpow_left_iff hl1).1 h2`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem depth_le (hl : l.Prime) (h : ModuliIntegralCharts.LinkConditions D P) (a b : ℝ)
    (ha : IsLUB S.thetaNorms ((l : ℝ) ^ (-a))) (hb : IsLUB S.germNorms ((l : ℝ) ^ (-b))) :
    a ≤ b + (P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y := by
  obtain ⟨_, H⟩ := h S.w l hl q DF S.nW S.hq S.hDF S.y
  obtain ⟨t, ht, hv⟩ := H S.sg S.hsg
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  have htpos : 0 < ‖t‖ := lt_of_lt_of_le (Real.rpow_pos_of_pos hl0 _) ht
  have key : ∀ u ∈ ModuliIntegralCharts.Ospan (C := ((P.loc S.w l).fld S.y).C)
      ((P.loc S.w l).secJet S.y ((P.loc S.w l).latStd S.nW) q DF S.sg), ‖S.ev u‖ ≤ (l : ℝ) ^ (-a) := by
    intro u hu
    unfold ModuliIntegralCharts.Ospan at hu
    induction hu using AddSubgroup.closure_induction with
    | mem u hu =>
      obtain ⟨α, hα, s, ⟨x, rfl⟩, rfl⟩ := hu
      rw [map_smul, smul_eq_mul, norm_mul]
      calc _ ≤ 1 * (l : ℝ) ^ (-a) := mul_le_mul hα (ha.1 ⟨x, rfl⟩) (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    | zero => rw [map_zero, norm_zero]; exact (Real.rpow_pos_of_pos hl0 _).le
    | add u v _ _ hu hv =>
      rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
    | neg u _ hu => rwa [map_neg, norm_neg]
  have ub : (l : ℝ) ^ (-b) ≤ (l : ℝ) ^ (-a) / ‖t‖ := hb.2 (by
    rintro _ ⟨v, hv', rfl⟩
    rw [le_div_iff₀ htpos]
    have := key _ (hv v hv')
    rwa [map_smul, smul_eq_mul, norm_mul, mul_comm] at this)
  have h2 : (l : ℝ) ^ (-b) ≤
      (l : ℝ) ^ (-a + (P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y) := by
    refine ub.trans ?_
    rw [div_le_iff₀ htpos, Real.rpow_add hl0, mul_assoc]
    have h3 : 1 ≤ (l : ℝ) ^ ((P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y) * ‖t‖ := by
      calc (1 : ℝ) = (l : ℝ) ^ ((P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y) *
            (l : ℝ) ^ (-((P.loc S.w l).cJ S.y q DF * (P.loc S.w l).phiCy S.y)) := by
              rw [← Real.rpow_add hl0]; simp
        _ ≤ _ := mul_le_mul_of_nonneg_left ht (Real.rpow_pos_of_pos hl0 _).le
    calc (l : ℝ) ^ (-a) = (l : ℝ) ^ (-a) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.rpow_pos_of_pos hl0 _).le
  have h4 := (Real.rpow_le_rpow_left_iff hl1).1 h2
  linarith

end JetSit

/- English proof (translation)
Unfold `ModuliIntegralCharts.Loc.phiCy ModuliIntegralCharts.phiC`. Apply `Real.sInf_nonneg` to reduce the goal to its premises. Introduce and unpack `x ⟨l, _, hpos, rfl⟩`. Distinguish the cases in `h0 : L.beS y = 0`. Rewrite using `[h0, map_zero]`.

Use `(hpos _ (fun a => ?_) h0).le` and prove the remaining obligations. Distinguish the cases in `ha : a = 0`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Conclude with `(L.be_pos y a ha).le`.
-/
theorem phiCy_nonneg {D : D7} {r j p : ℕ} (L : ModuliIntegralCharts.Loc D r j p) {Z : L.Mdl} (y : L.Pt Z) :
    0 ≤ L.phiCy y := by
  unfold ModuliIntegralCharts.Loc.phiCy ModuliIntegralCharts.phiC
  apply Real.sInf_nonneg
  rintro x ⟨l, _, hpos, rfl⟩
  by_cases h0 : L.beS y = 0
  · rw [h0, map_zero]
  · refine (hpos _ (fun a => ?_) h0).le
    by_cases ha : a = 0
    · subst ha; simp
    · exact (L.be_pos y a ha).le

/- English proof (translation)
Establish `h : (1 : ℤ) ≤ |NumberField.discr D.host.E|` using `Int.one_le_abs (NumberField.discr_ne_zero _)`. Establish `h2 : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr D.host.E| : ℤ) : ℝ)` using `by exact_mod_cast h`. Simplify using `using h2`.
-/
theorem one_le_absDiscr (D : D7) : (1 : ℝ) ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)| := by
  have h : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs (NumberField.discr_ne_zero _)
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|NumberField.discr D.host.E| : ℤ) : ℝ) := by exact_mod_cast h
  simpa using h2

/- English proof (translation)
Unfold `Host.rdE`. Conclude with `Real.one_le_rpow (one_le_absDiscr D) (by positivity)`.
-/
theorem one_le_rdE (D : D7) : 1 ≤ D.host.rdE := by
  unfold Host.rdE
  exact Real.one_le_rpow (one_le_absDiscr D) (by positivity)

/- English proof (translation)
Establish `hf : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Conclude with `this` after adjusting the coercions. Establish `hr : (1 : ℝ) ≤ D.R.r`. Establish `: 1 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.two_le_m; omega`.

Conclude with `this` after adjusting the coercions. Establish `hrd` using `one_le_rdE D`. Establish `hd' : (d : ℝ) ≤ 2 * D.R.f * D.R.r` using `by exact_mod_cast hd`. Establish `hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`. Establish `hL : 0 ≤ L.sc.L` using `by unfold Scale.L; exact (Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _).le`.

Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`. Use `set B : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L with hB`. Establish `hB1 : (D.R.f : ℝ) * D.R.r ≤ B` using `by rw [hB]; exact le_mul_of_one_le_right (by linarith) hL1`. Establish `hB3 : ((D.R.f : ℝ) * D.R.r) ^ 7 ≤ B ^ AP`. Combine the equalities or inequalities in the displayed calculation.

Establish `hRR : D.host.rdE ^ 2 ≤ sizeConstantAtParamsWeight.RR D Crr`. Unfold `sizeConstantAtParamsWeight.RR WeightFamilies.RRv`. Combine the equalities or inequalities in the displayed calculation. Establish `hPP : 16 * ((D.R.f : ℝ) * D.R.r) ^ 7 ≤ sizeConstantAtParamsWeight.PP D L CP AP`. Unfold `sizeConstantAtParamsWeight.PP placeRankTwoOne.PP`.

Rewrite using `[← hB]`. Establish `h0 : 0 ≤ ((D.R.f : ℝ) * D.R.r) ^ 7` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `h1 : (d : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 / 2 ≤ 16 * ((D.R.f : ℝ) * D.R.r) ^ 7`. Establish `hd2 : (d : ℝ) ^ 5 ≤ (2 * D.R.f * D.R.r) ^ 5` using `pow_le_pow_left₀ (Nat.cast_nonneg _) hd' 5`.

Establish `h2 : (d : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 ≤ (2 * D.R.f * D.R.r) ^ 5 * (D.R.f : ℝ) ^ 2` using `mul_le_mul_of_nonneg_right hd2 (by positivity)`. Establish `h3 : (2 * (D.R.f : ℝ) * D.R.r) ^ 5 * (D.R.f : ℝ) ^ 2 ≤ 32 * ((D.R.f : ℝ) * D.R.r) ^ 7`. Establish `e : (2 * (D.R.f : ℝ) * D.R.r) ^ 5 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 = 32 * ((D.R.f : ℝ) * D.R.r) ^ 7` using `by ring`. Establish `h4 : 0 ≤ (2 * (D.R.f : ℝ) * D.R.r) ^ 5 * (D.R.f : ℝ) ^ 2` using `by positivity`. Establish `hr2 : (1 : ℝ) ≤ (D.R.r : ℝ) ^ 2` using `one_le_pow₀ hr`.

Rewrite using `[← e]`. Conclude with `le_mul_of_one_le_right h4 hr2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h5 : 0 ≤ (d : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 / 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem Cd_le_RRPP (D : D7) (L : SizeData₂ D) (CP AP Crr : ℝ) (hR : 2 ≤ Crr) (hC : 16 ≤ CP) (hA : 7 ≤ AP)
    (d : ℕ) (hd : d ≤ 2 * D.R.f * D.R.r) :
    (d : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 * D.host.rdE ^ 2 / 2 ≤ sizeConstantAtParamsWeight.RR D Crr * sizeConstantAtParamsWeight.PP D L CP AP := by
  have hf : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hr : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hrd := one_le_rdE D
  have hd' : (d : ℝ) ≤ 2 * D.R.f * D.R.r := by exact_mod_cast hd
  have hfr : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
  have hL : 0 ≤ L.sc.L := by unfold Scale.L; exact (Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _).le
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  set B : ℝ := (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L with hB
  have hB1 : (D.R.f : ℝ) * D.R.r ≤ B := by rw [hB]; exact le_mul_of_one_le_right (by linarith) hL1
  have hB3 : ((D.R.f : ℝ) * D.R.r) ^ 7 ≤ B ^ AP := by
    calc ((D.R.f : ℝ) * D.R.r) ^ 7 ≤ B ^ 7 := pow_le_pow_left₀ (by linarith) hB1 7
      _ = B ^ (7 : ℝ) := by norm_cast
      _ ≤ B ^ AP := Real.rpow_le_rpow_of_exponent_le (by linarith) hA
  have hRR : D.host.rdE ^ 2 ≤ sizeConstantAtParamsWeight.RR D Crr := by
    unfold sizeConstantAtParamsWeight.RR WeightFamilies.RRv
    calc D.host.rdE ^ 2 = D.host.rdE ^ (2 : ℝ) := by norm_cast
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hrd hR
  have hPP : 16 * ((D.R.f : ℝ) * D.R.r) ^ 7 ≤ sizeConstantAtParamsWeight.PP D L CP AP := by
    unfold sizeConstantAtParamsWeight.PP placeRankTwoOne.PP
    rw [← hB]
    have h0 : 0 ≤ ((D.R.f : ℝ) * D.R.r) ^ 7 := by positivity
    nlinarith
  have h1 : (d : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 / 2 ≤ 16 * ((D.R.f : ℝ) * D.R.r) ^ 7 := by
    have hd2 : (d : ℝ) ^ 5 ≤ (2 * D.R.f * D.R.r) ^ 5 := pow_le_pow_left₀ (Nat.cast_nonneg _) hd' 5
    have h2 : (d : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 ≤ (2 * D.R.f * D.R.r) ^ 5 * (D.R.f : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_right hd2 (by positivity)
    have h3 : (2 * (D.R.f : ℝ) * D.R.r) ^ 5 * (D.R.f : ℝ) ^ 2 ≤ 32 * ((D.R.f : ℝ) * D.R.r) ^ 7 := by
      have e : (2 * (D.R.f : ℝ) * D.R.r) ^ 5 * (D.R.f : ℝ) ^ 2 * (D.R.r : ℝ) ^ 2 = 32 * ((D.R.f : ℝ) * D.R.r) ^ 7 := by ring
      have h4 : 0 ≤ (2 * (D.R.f : ℝ) * D.R.r) ^ 5 * (D.R.f : ℝ) ^ 2 := by positivity
      have hr2 : (1 : ℝ) ≤ (D.R.r : ℝ) ^ 2 := one_le_pow₀ hr
      rw [← e]
      exact le_mul_of_one_le_right h4 hr2
    linarith
  have h5 : 0 ≤ (d : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 / 2 := by positivity
  calc (d : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 * D.host.rdE ^ 2 / 2
      = D.host.rdE ^ 2 * ((d : ℝ) ^ 5 * (D.R.f : ℝ) ^ 2 / 2) := by ring
    _ ≤ sizeConstantAtParamsWeight.RR D Crr * sizeConstantAtParamsWeight.PP D L CP AP :=
      mul_le_mul hRR (h1.trans hPP) h5 (le_trans (by positivity) hRR)

section A5

variable {D : D7} (L : SizeData₂ D) {V : DivX D} {Lc : placeRankTwoOne.Loc D V} (X : sizeConstantAtParamsWeight.Loc D V Lc)

structure TieJet (P : ModuliIntegralCharts.Prov D) where
  sit : ∀ s : X.ThF, (X.thF s).l.Prime → Nat.Coprime (X.thF s).l (X.thF s).q →
    JetSit D P (X.thF s).l (X.thF s).q (X.thF s).DF
  phic_eq : ∀ s h1 h2, (X.thF s).phic = (P.loc (sit s h1 h2).w (X.thF s).l).phiCy (sit s h1 h2).y
  theta_def : ∀ s h1 h2, IsLUB (sit s h1 h2).thetaNorms (((X.thF s).l : ℝ) ^ (-(X.thF s).minVTheta))
  nuLoc_def : ∀ s h1 h2, IsLUB (sit s h1 h2).germNorms (((X.thF s).l : ℝ) ^ (-(X.thF s).nuLoc))
  rk_le : ∀ s h1 h2, (P.loc (sit s h1 h2).w (X.thF s).l).dP (sit s h1 h2).y ≤ 2 * D.R.f * D.R.r

def FieldSizeClauses (CP AP Crr : ℝ) : Prop :=
  (∀ s : X.ThF, (X.thF s).l.Prime → 0 < (X.thF s).q →
    (X.thF s).lamQ ^ 2 ≤ sizeConstantAtParamsWeight.RR D Crr * sizeConstantAtParamsWeight.PP D L CP AP * (X.thF s).phic ∧
    ((X.thF s).r1.Prime → (X.thF s).r1 ≠ 2 → jacobiSym (-(D.host.d : ℤ)) (X.thF s).r1 = 1 →
      Nat.Coprime (X.thF s).r1 (X.thF s).q → ((X.thF s).r1 : ℝ) ≤ L.sc.L →
      ((X.thF s).r1 : ℝ) ^ (-(4 : ℤ)) * (X.thF s).phic -
        (if (X.thF s).l = (X.thF s).r1 then sizeConstantAtParamsWeight.PP D L CP AP else 0) ≤ (X.thF s).vTau)) ∧
  (∀ s : X.ThA, 0 < (X.thA s).q → sizeConstantAtParamsWeight.QNorm D (X.thA s).q → sizeConstantAtParamsWeight.TheoremI2Hypotheses D L CP AP Crr (X.thA s).q (X.thA s).DF →
    -(sizeConstantAtParamsWeight.PP D L CP AP * (X.thA s).DF) -
        sizeConstantAtParamsWeight.RR D Crr * sizeConstantAtParamsWeight.PP D L CP AP * ((X.thA s).DF : ℝ) ^ 2 / ((X.thA s).q : ℝ) * (X.thA s).phic
      ≤ (X.thA s).logThetaMax ∧
    ((X.thA s).r1.Prime → (X.thA s).r1 ≠ 2 → jacobiSym (-(D.host.d : ℤ)) (X.thA s).r1 = 1 →
      Nat.Coprime (X.thA s).r1 (X.thA s).q → ((X.thA s).r1 : ℝ) ≤ L.sc.L →
      ((X.thA s).r1 : ℝ) ^ (-(4 : ℤ)) * (X.thA s).phic - sizeConstantAtParamsWeight.PP D L CP AP ≤ (X.thA s).cuspVal))

/- English proof (translation)
Establish `h1` using `(T.sit s hl hc).depth_le hl h _ _ (T.theta_def s hl hc) (T.nuLoc_def s hl hc)`. Establish `hφ` using `phiCy_nonneg (P.loc (T.sit s hl hc).w (X.thF s).l) (T.sit s hl hc).y`. Establish `hK` using `Cd_le_RRPP D L CP AP Crr hR hC hA _ (T.rk_le s hl hc)`. Rewrite using `[T.phic_eq s hl hc]`. Use `h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ hφ))` and prove the remaining obligations.

Unfold `ModuliIntegralCharts.Loc.cJ`. Conclude with `div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) (Nat.cast_nonneg _)`.
-/
theorem theta_valuation_bound_of {P : ModuliIntegralCharts.Prov D} (T : TieJet X P) (CP AP Crr : ℝ) (hR : 2 ≤ Crr) (hC : 16 ≤ CP)
    (hA : 7 ≤ AP) (h : ModuliIntegralCharts.LinkConditions D P) (s : X.ThF) (hl : (X.thF s).l.Prime)
    (hc : Nat.Coprime (X.thF s).l (X.thF s).q) :
    (X.thF s).minVTheta ≤ (X.thF s).nuLoc +
      sizeConstantAtParamsWeight.RR D Crr * sizeConstantAtParamsWeight.PP D L CP AP * ((X.thF s).DF : ℝ) ^ 2 / ((X.thF s).q : ℝ) * (X.thF s).phic := by
  have h1 := (T.sit s hl hc).depth_le hl h _ _ (T.theta_def s hl hc) (T.nuLoc_def s hl hc)
  have hφ := phiCy_nonneg (P.loc (T.sit s hl hc).w (X.thF s).l) (T.sit s hl hc).y
  have hK := Cd_le_RRPP D L CP AP Crr hR hC hA _ (T.rk_le s hl hc)
  rw [T.phic_eq s hl hc]
  refine h1.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ hφ))
  unfold ModuliIntegralCharts.Loc.cJ
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hK (by positivity)) (Nat.cast_nonneg _)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun s hl hq => ⟨(hr.1 s hl hq).1, fun hN _ => theta_valuation_bound_of L X T CP AP Crr hR hC hA h s hl hN.2.1.symm, (hr.1 s hl hq).2⟩, hr.2⟩`.
-/
theorem theta_field_admissible_of_jet {P : ModuliIntegralCharts.Prov D} (T : TieJet X P) (CP AP Crr : ℝ) (hR : 2 ≤ Crr) (hC : 16 ≤ CP)
    (hA : 7 ≤ AP) (h : ModuliIntegralCharts.LinkConditions D P) (hr : FieldSizeClauses L X CP AP Crr) :
    sizeConstantAtParamsWeight.adm5 D L V Lc X CP AP Crr :=
  ⟨fun s hl hq => ⟨(hr.1 s hl hq).1, fun hN _ => theta_valuation_bound_of L X T CP AP Crr hR hC hA h s hl hN.2.1.symm,
    (hr.1 s hl hq).2⟩, hr.2⟩

/- English proof (translation)
The claim follows from `theta_field_admissible_of_jet L X T CP AP Crr hR hC hA h hr`.
-/
theorem theta_field_admissible_of_jet_form {P : ModuliIntegralCharts.Prov D} (T : TieJet X P) (CP AP Crr : ℝ) (hR : 2 ≤ Crr) (hC : 16 ≤ CP)
    (hA : 7 ≤ AP) (h : BoundaryLocalData.Conclusion5 D P) (hr : FieldSizeClauses L X CP AP Crr) :
    sizeConstantAtParamsWeight.adm5 D L V Lc X CP AP Crr := theta_field_admissible_of_jet L X T CP AP Crr hR hC hA h hr

end A5

section A5F

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Y : sizeConstantAtParamsWeight.LocF Fm)

/- English proof (translation)
Take `⟨x0, h0⟩` from `hr`. Conclude with `⟨x0, fun x h1 hx i => theta_field_admissible_of_jet (Fm.L x i) (Y.lo x h1 i) (T x h1 i) CP AP Crr hR hC hA (s66 a66 x h1 i).1.2.2.2.2.2.2.2.1 (h0 x h1 hx i)⟩`.
-/
theorem theta_field_admissible_family_of (PF : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ModuliIntegralCharts.Prov (Fm.D x i))
    (T : ∀ x (h1 : Fm.x1 < x) (i : Fm.Ix x), TieJet (Y.lo x h1 i) (PF x h1 i)) (ka CP AP Crr : ℝ) (hR : 2 ≤ Crr) (hC : 16 ≤ CP)
    (hA : 7 ≤ AP) (s66 : ModuliIntegralCharts.FamilyPacketImplication Fm PF ka) (a66 : ∀ x hx i, ModuliIntegralCharts.admitted (Fm.D x i) (PF x hx i))
    (hr : ∃ x0 : ℝ, ∀ x (h1 : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, FieldSizeClauses (Fm.L x i) (Y.lo x h1 i) CP AP Crr) :
    ∃ x0 : ℝ, ∀ x (h1 : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      sizeConstantAtParamsWeight.adm5 (Fm.D x i) (Fm.L x i) (Fm.X x i) (Y.fl x h1 i) (Y.lo x h1 i) CP AP Crr := by
  obtain ⟨x0, h0⟩ := hr
  exact ⟨x0, fun x h1 hx i => theta_field_admissible_of_jet (Fm.L x i) (Y.lo x h1 i) (T x h1 i) CP AP Crr hR hC hA
    (s66 a66 x h1 i).1.2.2.2.2.2.2.2.1 (h0 x h1 hx i)⟩

end A5F

section A5ab

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (Y : sizeConstantAtParamsWeight.LocF Fm)
  (XF : IntegralModelsLocalData.ProvF Fm) (YF : BoundaryLocalData.ProvF Fm (fun x hx i => (XF x hx i).P))

def BoundaryLocalHypothesesAlongFamily : Prop :=
  ∀ x hx (i : Fm.Ix x), BoundaryLocalData.adm3 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.ArchimedeanSignatureMatching (Fm.D x i) (XF x hx i).P (YF x hx i) ∧ BoundaryLocalData.adm5 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.adm6 (Fm.D x i) (XF x hx i).P ∧ BoundaryLocalData.adm7 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.adm8 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧ BoundaryLocalData.adm9 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.adm10 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧ BoundaryLocalData.adm11 (Fm.D x i) (XF x hx i).P (YF x hx i) ∧
    BoundaryLocalData.adm12 (Fm.D x i) (XF x hx i).P (YF x hx i)

/- English proof (translation)
Introduce `x hx i`. Take `⟨-, hC, hNV, hTR, hORD, -⟩` from `h x hx i`. Take `⟨l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩` from `lv x hx i`. Conclude with `⟨hTR, Formalism.HadamardInequality.P.transference_principle, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, hC, hNV, hORD, (a x hx i).1⟩`.
-/
theorem prismatic_admissible_family_of_crystal (a : IntegralModelsLocalData.AdmFx Fm XF) (h : IntegralModelsLocalData.familyPoincareExtensionAndPointBounds Fm XF) (lv : BoundaryLocalHypothesesAlongFamily Fm XF YF) :
    BoundaryLocalData.AdmFx Fm (fun x hx i => (XF x hx i).P) YF := by
  intro x hx i
  obtain ⟨-, hC, hNV, hTR, hORD, -⟩ := h x hx i
  obtain ⟨l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := lv x hx i
  exact ⟨hTR, Formalism.HadamardInequality.P.transference_principle, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12, hC, hNV, hORD, (a x hx i).1⟩

/- English proof (translation)
Introduce `x hx i` and use `(sb (prismatic_admissible_family_of_crystal Fm XF YF a (sa a) lv) x hx i).2.2.2.2`.
-/
theorem jet_family_of_crystal_parts (ka : ℝ) (sa : IntegralModelsLocalData.FamilyPacketImplication Fm XF) (sb : BoundaryLocalData.FamilyKeyFormulaOfAdmissible Fm (fun x hx i => (XF x hx i).P) YF ka)
    (a : IntegralModelsLocalData.AdmFx Fm XF) (lv : BoundaryLocalHypothesesAlongFamily Fm XF YF) :
    ∀ x hx (i : Fm.Ix x), ModuliIntegralCharts.LinkConditions (Fm.D x i) (XF x hx i).P :=
  fun x hx i => (sb (prismatic_admissible_family_of_crystal Fm XF YF a (sa a) lv) x hx i).2.2.2.2

/- English proof (translation)
Take `⟨x0, h0⟩` from `lf`. Use `⟨x0, fun x h1 hx i => ?_⟩` and prove the remaining obligations. Take `⟨h3, h5, h6, h9⟩` from `h0 x h1 hx i`. Conclude with `⟨h3, theta_field_admissible_of_jet (Fm.L x i) (Y.lo x h1 i) (T x h1 i) Ca Aa Ra hR hC hA (jet_family_of_crystal_parts Fm XF YF ka sa sb a lv x h1 i) h5, h6, h9⟩`.
-/
theorem leaves_family_of_crystal_parts (T : ∀ x (h1 : Fm.x1 < x) (i : Fm.Ix x), TieJet (Y.lo x h1 i) (XF x h1 i).P) (ka Ca Aa Ra : ℝ)
    (hR : 2 ≤ Ra) (hC : 16 ≤ Ca) (hA : 7 ≤ Aa)
    (sa : IntegralModelsLocalData.FamilyPacketImplication Fm XF) (sb : BoundaryLocalData.FamilyKeyFormulaOfAdmissible Fm (fun x hx i => (XF x hx i).P) YF ka)
    (a : IntegralModelsLocalData.AdmFx Fm XF) (lv : BoundaryLocalHypothesesAlongFamily Fm XF YF)
    (lf : ∃ x0 : ℝ, ∀ x (h1 : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      sizeConstantAtParamsWeight.adm3 (Fm.D x i) (Fm.X x i) (Y.fl x h1 i) (Y.lo x h1 i) ∧
      FieldSizeClauses (Fm.L x i) (Y.lo x h1 i) Ca Aa Ra ∧
      sizeConstantAtParamsWeight.adm6 (Fm.D x i) (Fm.X x i) (Y.fl x h1 i) (Y.lo x h1 i) ∧
      sizeConstantAtParamsWeight.adm9 (Fm.D x i) (Fm.L x i) (Fm.X x i) (Y.fl x h1 i) (Y.lo x h1 i) Ca Aa Ra) :
    ∃ x0 : ℝ, ∀ x (h1 : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      sizeConstantAtParamsWeight.adm3 (Fm.D x i) (Fm.X x i) (Y.fl x h1 i) (Y.lo x h1 i) ∧
      sizeConstantAtParamsWeight.adm5 (Fm.D x i) (Fm.L x i) (Fm.X x i) (Y.fl x h1 i) (Y.lo x h1 i) Ca Aa Ra ∧
      sizeConstantAtParamsWeight.adm6 (Fm.D x i) (Fm.X x i) (Y.fl x h1 i) (Y.lo x h1 i) ∧
      sizeConstantAtParamsWeight.adm9 (Fm.D x i) (Fm.L x i) (Fm.X x i) (Y.fl x h1 i) (Y.lo x h1 i) Ca Aa Ra := by
  obtain ⟨x0, h0⟩ := lf
  refine ⟨x0, fun x h1 hx i => ?_⟩
  obtain ⟨h3, h5, h6, h9⟩ := h0 x h1 hx i
  exact ⟨h3, theta_field_admissible_of_jet (Fm.L x i) (Y.lo x h1 i) (T x h1 i) Ca Aa Ra hR hC hA
    (jet_family_of_crystal_parts Fm XF YF ka sa sb a lv x h1 i) h5, h6, h9⟩

end A5ab

/- English proof (translation)
Establish `hx0 : 0 < x` using `by linarith`. Establish `hc : 0 < 2 / e` using `by positivity`. Establish `hy : 2 / e + 2 ≤ x ^ (e / 2)`. Establish `h1 : ((2 / e + 2) ^ (2 / e)) ^ (e / 2) ≤ x ^ (e / 2)` using `Real.rpow_le_rpow (by positivity) hx (by positivity)`. Rewrite `h1` using `[← Real.rpow_mul (by positivity)]`.

Establish `h2 : 2 / e * (e / 2) = 1` using `by field_simp`. Rewrite `h1` using `[h2, Real.rpow_one]`. Then use the resulting hypothesis. Establish `hlog : Real.log x ≤ 2 / e * x ^ (e / 2)`. Establish `h` using `Real.log_le_rpow_div hx0.le (show 0 < e / 2 by positivity)`. Establish `h2 : x ^ (e / 2) / (e / 2) = 2 / e * x ^ (e / 2)` using `by field_simp`.

Rewrite `h` using `[h2]`. Then use the resulting hypothesis. Establish `hsq : x ^ e = x ^ (e / 2) * x ^ (e / 2)`. Rewrite using `[← Real.rpow_add hx0]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `h4 : Real.log 4 ≤ 3`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith` as an intermediate fact. Rewrite using `[Real.log_mul (by norm_num) hx0.ne', hsq]`. Establish `hy0 : 0 ≤ x ^ (e / 2)` using `by linarith`. Establish `h5 : (2 / e + 2) * x ^ (e / 2) ≤ x ^ (e / 2) * x ^ (e / 2)` using `mul_le_mul_of_nonneg_right hy hy0`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem log_four_mul_le_rpow (e x : ℝ) (he : 0 < e) (hx1 : 1 < x) (hx : (2 / e + 2) ^ (2 / e) ≤ x) :
    Real.log (4 * x) ≤ x ^ e := by
  have hx0 : 0 < x := by linarith
  have hc : 0 < 2 / e := by positivity
  have hy : 2 / e + 2 ≤ x ^ (e / 2) := by
    have h1 : ((2 / e + 2) ^ (2 / e)) ^ (e / 2) ≤ x ^ (e / 2) :=
      Real.rpow_le_rpow (by positivity) hx (by positivity)
    rw [← Real.rpow_mul (by positivity)] at h1
    have h2 : 2 / e * (e / 2) = 1 := by field_simp
    rwa [h2, Real.rpow_one] at h1
  have hlog : Real.log x ≤ 2 / e * x ^ (e / 2) := by
    have h := Real.log_le_rpow_div hx0.le (show 0 < e / 2 by positivity)
    have h2 : x ^ (e / 2) / (e / 2) = 2 / e * x ^ (e / 2) := by field_simp
    rwa [h2] at h
  have hsq : x ^ e = x ^ (e / 2) * x ^ (e / 2) := by
    rw [← Real.rpow_add hx0]; congr 1; ring
  have h4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num); linarith
  rw [Real.log_mul (by norm_num) hx0.ne', hsq]
  have hy0 : 0 ≤ x ^ (e / 2) := by linarith
  have h5 : (2 / e + 2) * x ^ (e / 2) ≤ x ^ (e / 2) * x ^ (e / 2) := mul_le_mul_of_nonneg_right hy hy0
  nlinarith

/- English proof (translation)
Establish `h0` using `D.host.der.rd_sq_ge`. Establish `h1 : (1 : ℝ) ≤ D.R.ord` using `by exact_mod_cast D.R.ord_pos`. Establish `h2 : (0 : ℝ) ≤ D.host.rd` using `Real.rpow_nonneg (abs_nonneg _) _`. Use `show 2 ≤ D.host.rd`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem two_le_rdE (D : D7) (_hq : 2 ≤ D.host.q) (_hd : 2 ≤ D.host.d) : 2 ≤ D.host.rdE := by
  have h0 := D.host.der.rd_sq_ge
  have h1 : (1 : ℝ) ≤ D.R.ord := by exact_mod_cast D.R.ord_pos
  have h2 : (0 : ℝ) ≤ D.host.rd := Real.rpow_nonneg (abs_nonneg _) _
  show 2 ≤ D.host.rd
  nlinarith

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Establish `h1 : n = 0 ∨ n = 1` using `by omega`. Apply the tactic sequence `rcases h1 with rfl | rfl <;> simp at h`.
-/
theorem two_le_of_log_pos (n : ℕ) (h : 0 < Real.log (n : ℝ)) : 2 ≤ n := by
  by_contra hn
  have h1 : n = 0 ∨ n = 1 := by omega
  rcases h1 with rfl | rfl <;> simp at h

/- English proof (translation)
Take `⟨-, -, -, -, -, hCond, hQD, -, hLa, hRho, hBot, -, -, hEta, hNodes, -, hDel, -⟩` from `hS`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hq2 : 2 ≤ D.host.q` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)`.

Establish `hd2 : 2 ≤ D.host.d` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)`. Establish `hq' : (2 : ℝ) ≤ D.host.q` using `by exact_mod_cast hq2`. Establish `hd' : (2 : ℝ) ≤ D.host.d` using `by exact_mod_cast hd2`. Establish `hrd2` using `two_le_rdE D hq2 hd2`. Establish `hn1 : (1 : ℝ) ≤ D.R.n`.

Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions. Establish `ht1 : (1 : ℝ) ≤ D.R.t`. Establish `: 1 ≤ D.R.t` using `by have := D.R.rank_add_five_le; omega`. Conclude with `this` after adjusting the coercions.

Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hk0 : (0 : ℝ) < D.R.k`. Establish `: 0 < D.R.k` using `by have := D.R.m_add_three_le_k; omega`.

Conclude with `this` after adjusting the coercions. Establish `hb1 : 1 ≤ L.sc.b` using `by unfold Scale.b; exact Real.one_le_exp (by linarith)`. Establish `hm0 : (0 : ℝ) ≤ D.R.m` using `by linarith`. Use `⟨?_, ?_, ?_, hx4, hx5, ?_, ?_, hCc, P.uk_extreme, ?_, hEta.1, hEta.2.2.2.2.1, hDel.2.2.2.1, ?_⟩` and prove the remaining obligations. Unfold `Host.v; exact Real.log_nonneg (by linarith)`.

Establish `hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d` using `by nlinarith`. Establish `hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`. Establish `hc : D.host.rdE ≤ Formalism.MainNotions.szCond L`. Use `hQD.2.2.2.2.2.2.2.trans ?_` and prove the remaining obligations. Unfold `Formalism.MainNotions.szCond`.

Establish `: (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d)` using `mul_le_mul_of_nonneg_left hs (by positivity)`. Establish `h0 : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hc1 : 1 ≤ Formalism.MainNotions.szCond L` using `by linarith`. Establish `h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36` using `le_self_pow₀ hc1 (by norm_num)`.

Establish `h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150` using `le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)`. Establish `hsb : Real.sqrt L.sc.b ≤ L.sc.b` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`. Establish `hfin : D.host.rdE ≤ L.sc.b` using `hc.trans (h36.trans (h150.trans (hCond.trans hsb)))`. Use `Real.log_le_log (by linarith) hfin` as an intermediate fact. Rewrite `this` using `[show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _]`. Then use the resulting hypothesis.

Conclude with `hQD.2.2.2.2.2.1`. Introduce `i`. Take `⟨Y, hY1, -, hY3, hY4⟩` from `P.g_Y`. Establish `hY0 : 0 < Y` using `lt_of_lt_of_le (by positivity) hY1`. Establish `hg0 : (0 : ℝ) < D.host.g i` using `lt_of_lt_of_le hY0 (hY4 i).1`.

Establish `h1` using `Real.log_le_log hg0 (hY4 i).2`. Rewrite `h1` using `[Real.log_mul (by norm_num) hY0.ne']`. Establish `h2 : Real.log 2 ≤ 1`. Use `Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith` as an intermediate fact. Establish `h3 : (P.CYL + 1) * L.sc.L ≤ Cs * L.sc.L` using `mul_le_mul_of_nonneg_right h6 (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities. Introduce `u`. Use `(hT u).trans ?_` and prove the remaining obligations. Conclude with `mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCT hm0) (by linarith)`. Establish `h1` using `hNodes.2.2.2.1`.

Establish `h2 : L.etaSz / D.R.m ≤ L.etaSz` using `div_le_self L.etaSz_pos.le hm1`. Unfold `placeRankTwoOne.NN`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `t`. Establish `h1` using `hBot t`.

Establish `hLa0 : 0 ≤ L.LaG` using `le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1`. Establish `h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k` using `div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 _).le (Real.log_nonneg hx1.le)) hLa0) hk0.le`. Establish `h3 : L.sc.x ^ (-2 : ℝ) ≤ 1` using `Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)`. Establish `hb' : 0 ≤ L.sc.b'`. Unfold `Scale.b' Scale.a Scale.X' Scale.b`.

Check the signs of the components of the expression. Establish `hR : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k + L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤ L.sc.x ^ (-2 : ℝ)` using `hRho`. Establish `h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1`. Establish `: 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k = 4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k)` using `by ring`. Establish `h0 : 0 ≤ Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k`.

Unfold `Formalism.MainNotions.szNst Scale.delta1`. Use `Real.rpow_pos_of_pos hx0 (-(L.sc.eps / 8))` as an intermediate fact. Use `Real.rpow_pos_of_pos hx0 L.sc.eps` as an intermediate fact. Check the signs of the components of the expression. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k = Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k * L.sc.b'` using `by ring`. Rewrite `h1` using `[h5]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sizes_of_magnitudes (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (hS : Formalism.MainNotions.SizesAt L) (Cs CTu : ℝ)
    (h6 : P.CYL + 1 ≤ Cs) (hCT : CTu ≤ Cs) (hCc : L.Cc ≤ Cs)
    (hT : ∀ u, Real.log ((D.mem u).A.T : ℝ) ≤ CTu * D.R.m * L.sc.L)
    (hx4 : Real.log (4 * L.sc.x) ≤ L.sc.L) (hx5 : 1 ≤ Real.log (Real.log L.sc.x)) :
    placeRankTwoOne.Sizes D L Cs := by
  obtain ⟨-, -, -, -, -, hCond, hQD, -, hLa, hRho, hBot, -, -, hEta, hNodes, -, hDel, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hq2 : 2 ≤ D.host.q := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 : 2 ≤ D.host.d := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
  have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
  have hrd2 := two_le_rdE D hq2 hd2
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  have hm0 : (0 : ℝ) ≤ D.R.m := by linarith
  refine ⟨?_, ?_, ?_, hx4, hx5, ?_, ?_, hCc, P.uk_extreme, ?_, hEta.1, hEta.2.2.2.2.1, hDel.2.2.2.1, ?_⟩
  · unfold Host.v; exact Real.log_nonneg (by linarith)
  ·
    have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
    have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
      Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hc : D.host.rdE ≤ Formalism.MainNotions.szCond L := by
      refine hQD.2.2.2.2.2.2.2.trans ?_
      unfold Formalism.MainNotions.szCond
      have : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
          (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hs (by positivity)
      have h0 : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
      nlinarith
    have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by linarith
    have h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
    have h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
      le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
    have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
    have hfin : D.host.rdE ≤ L.sc.b := hc.trans (h36.trans (h150.trans (hCond.trans hsb)))
    have := Real.log_le_log (by linarith) hfin
    rwa [show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _] at this
  · exact hQD.2.2.2.2.2.1
  · intro i
    obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
    have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY1
    have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le hY0 (hY4 i).1
    have h1 := Real.log_le_log hg0 (hY4 i).2
    rw [Real.log_mul (by norm_num) hY0.ne'] at h1
    have h2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
    have h3 : (P.CYL + 1) * L.sc.L ≤ Cs * L.sc.L := mul_le_mul_of_nonneg_right h6 (by linarith)
    nlinarith
  · intro u
    refine (hT u).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCT hm0) (by linarith)
  · have h1 := hNodes.2.2.2.1
    have h2 : L.etaSz / D.R.m ≤ L.etaSz := div_le_self L.etaSz_pos.le hm1
    unfold placeRankTwoOne.NN
    linarith
  · intro t
    have h1 := hBot t
    have hLa0 : 0 ≤ L.LaG := le_trans (Real.rpow_pos_of_pos hx0 _).le hLa.1
    have h2 : 0 ≤ L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k :=
      div_nonneg (mul_nonneg (mul_nonneg (Real.rpow_pos_of_pos hx0 _).le (Real.log_nonneg hx1.le)) hLa0) hk0.le
    have h3 : L.sc.x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1.le (by norm_num)
    have hb' : 0 ≤ L.sc.b' := by
      unfold Scale.b' Scale.a Scale.X' Scale.b
      positivity
    have hR : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k +
        L.sc.x ^ Formalism.MainNotions.szTh L * Real.log L.sc.x * L.LaG / D.R.k ≤ L.sc.x ^ (-2 : ℝ) := hRho
    have h4 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k ≤ 1 := by
      have : 4 * Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k =
          4 * (Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k) := by ring
      have h0 : 0 ≤ Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k := by
        unfold Formalism.MainNotions.szNst Scale.delta1
        have := Real.rpow_pos_of_pos hx0 (-(L.sc.eps / 8))
        have := Real.rpow_pos_of_pos hx0 L.sc.eps
        positivity
      linarith
    have h5 : Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG * L.sc.b' / D.R.k =
        Formalism.MainNotions.szNst L * L.sc.x ^ L.sc.eps * L.LaG / D.R.k * L.sc.b' := by ring
    rw [h5] at h1
    nlinarith

section SizesF

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def CsFn (l : List ℝ) : ℝ := max (l.getD 6 0 + 1) (max (l.getD 13 0) (max (l.getD 1 0) 0))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem CsFn_cOut : CsFn Fm.cOut = max (Fm.CYL + 1) (max Fm.CTu (max Fm.Cc 0)) := rfl

/- English proof (translation)
The claim follows from `le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))`.
-/
theorem CsFn_nonneg (l : List ℝ) : 0 ≤ CsFn l :=
  le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

/- English proof (translation)
Take `⟨xT, hT⟩` from `hTu`. Establish `he : 0 < eps`. Take `⟨i⟩` from `Fm.Ix_zero`. Rewrite using `[← Fm.L_eps 0 i]`. Conclude with `(Fm.L 0 i).sc.eps_pos`.

Use `⟨max xT (max (Real.exp (Real.exp 1)) ((2 / eps + 2) ^ (2 / eps))), fun x hx h1 i => ?_⟩` and prove the remaining obligations. Establish `ha : xT ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hb : Real.exp (Real.exp 1) ≤ x` using `le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx`. Establish `hc : (2 / eps + 2) ^ (2 / eps) ≤ x` using `le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx`. Establish `hx1 : 1 < x` using `lt_trans Fm.one_lt_family_threshold h1`.

Rewrite using `[CsFn_cOut]`. Use `sizes_of_magnitudes _ _ (Fm.params x h1 i) (Fm.sizes x h1 i) _ Fm.CTu ?_ ?_ ?_ (hT x ha i).2 ?_ ?_` and prove the remaining obligations. Rewrite using `[Fm.params_CYL x h1 i]`. Conclude with `le_max_left _ _`. Conclude with `le_trans (le_max_left _ _) (le_max_right _ _)`.

Rewrite using `[Fm.Cc_eq x i]`. Conclude with `le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))`. Unfold `Scale.L`. Rewrite using `[Fm.L_x x i h1, Fm.L_eps x i]`. Conclude with `log_four_mul_le_rpow eps x he hx1 hc`.

Rewrite using `[Fm.L_x x i h1]`. Establish `h2 : Real.exp 1 ≤ Real.log x`. Rewrite using `[Real.le_log_iff_exp_le (by linarith)]; exact hb`. Rewrite using `[Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h2)]`. Conclude with `h2`.
-/
theorem sizes_family_eventually (hTu : Formalism.MainNotions.TuSize Fm) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ _ : Fm.x1 < x, ∀ i : Fm.Ix x,
      placeRankTwoOne.Sizes (Fm.D x i) (Fm.L x i) (CsFn Fm.cOut) := by
  obtain ⟨xT, hT⟩ := hTu
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  refine ⟨max xT (max (Real.exp (Real.exp 1)) ((2 / eps + 2) ^ (2 / eps))), fun x hx h1 i => ?_⟩
  have ha : xT ≤ x := le_trans (le_max_left _ _) hx
  have hb : Real.exp (Real.exp 1) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hc : (2 / eps + 2) ^ (2 / eps) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hx1 : 1 < x := lt_trans Fm.one_lt_family_threshold h1
  rw [CsFn_cOut]
  refine sizes_of_magnitudes _ _ (Fm.params x h1 i) (Fm.sizes x h1 i) _ Fm.CTu ?_ ?_ ?_ (hT x ha i).2 ?_ ?_
  · rw [Fm.params_CYL x h1 i]; exact le_max_left _ _
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · rw [Fm.Cc_eq x i]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  · unfold Scale.L
    rw [Fm.L_x x i h1, Fm.L_eps x i]
    exact log_four_mul_le_rpow eps x he hx1 hc
  · rw [Fm.L_x x i h1]
    have h2 : Real.exp 1 ≤ Real.log x := by
      rw [Real.le_log_iff_exp_le (by linarith)]; exact hb
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos _) h2)]; exact h2

end SizesF

/- English proof (translation)
Establish `hL0 : 0 ≤ L.sc.L`. Unfold `Scale.L; exact (Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _).le`. Establish `hb1 : 1 ≤ L.sc.b` using `by unfold Scale.b; exact Real.one_le_exp hL0`. Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`.

Conclude with `this` after adjusting the coercions. Establish `hf : (D.R.f : ℝ) ≤ D.R.k`. Establish `: D.R.f ≤ D.R.k` using `by unfold Ranks.f Ranks.n; exact D.R.f_le_k`. Conclude with `this` after adjusting the coercions. Establish `hr : (D.R.r : ℝ) ≤ 2 * D.R.k`.

Establish `: D.R.r ≤ 2 * D.R.k` using `by unfold Ranks.r; have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hg : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ)`. Rewrite using `[Nat.cast_min]`. Conclude with `le_min (hG 0 0).1 (hG 1 1).1`.

Establish `hkb : (D.R.k : ℝ) ^ 2 * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8`. Rewrite using `[mul_pow]`. Conclude with `mul_le_mul (pow_le_pow_right₀ hk1 (by norm_num)) (le_self_pow₀ hb1 (by norm_num)) (by linarith) (by positivity)`. Establish `hg0 : (0 : ℝ) < ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ)` using `lt_of_lt_of_le (by positivity) (hkb.trans hg)`. Establish `hb0 : 0 < L.sc.b` using `by linarith`.

Establish `hq : (D.R.f : ℝ) * D.R.r / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) ≤ 2 / L.sc.b`. Rewrite using `[div_le_div_iff₀ hg0 hb0]`. Establish `h1 : (D.R.f : ℝ) * D.R.r ≤ D.R.k * (2 * D.R.k)` using `mul_le_mul hf hr (Nat.cast_nonneg _) (by linarith)`. Establish `h2 : (D.R.f : ℝ) * D.R.r * L.sc.b ≤ D.R.k * (2 * D.R.k) * L.sc.b` using `mul_le_mul_of_nonneg_right h1 hb0.le`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hq0 : 0 ≤ (D.R.f : ℝ) * D.R.r / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ)` using `by positivity`. Distinguish the cases in `hC : CT ≤ 0`. Use `mul_nonpos_of_nonpos_of_nonneg hC hq0` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `push Not at hC`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem delT_of (D : D7) (L : SizeData₂ D) (hG : Formalism.MainNotions.SizeG L) (CT : ℝ) (hb : 6 * CT ≤ L.sc.b) :
    CT * ((D.R.f : ℝ) * D.R.r / (min (D.host.g 0) (D.host.g 1) : ℕ)) ≤ 1 / 3 := by
  have hL0 : 0 ≤ L.sc.L := by
    unfold Scale.L; exact (Real.rpow_pos_of_pos (by linarith [L.sc.one_lt_alt]) _).le
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp hL0
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hf : (D.R.f : ℝ) ≤ D.R.k := by
    have : D.R.f ≤ D.R.k := by unfold Ranks.f Ranks.n; exact D.R.f_le_k
    exact_mod_cast this
  have hr : (D.R.r : ℝ) ≤ 2 * D.R.k := by
    have : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hg : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) := by
    rw [Nat.cast_min]; exact le_min (hG 0 0).1 (hG 1 1).1
  have hkb : (D.R.k : ℝ) ^ 2 * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := by
    rw [mul_pow]
    exact mul_le_mul (pow_le_pow_right₀ hk1 (by norm_num)) (le_self_pow₀ hb1 (by norm_num)) (by linarith)
      (by positivity)
  have hg0 : (0 : ℝ) < ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) :=
    lt_of_lt_of_le (by positivity) (hkb.trans hg)
  have hb0 : 0 < L.sc.b := by linarith
  have hq : (D.R.f : ℝ) * D.R.r / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) ≤ 2 / L.sc.b := by
    rw [div_le_div_iff₀ hg0 hb0]
    have h1 : (D.R.f : ℝ) * D.R.r ≤ D.R.k * (2 * D.R.k) :=
      mul_le_mul hf hr (Nat.cast_nonneg _) (by linarith)
    have h2 : (D.R.f : ℝ) * D.R.r * L.sc.b ≤ D.R.k * (2 * D.R.k) * L.sc.b :=
      mul_le_mul_of_nonneg_right h1 hb0.le
    nlinarith
  have hq0 : 0 ≤ (D.R.f : ℝ) * D.R.r / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ) := by positivity
  by_cases hC : CT ≤ 0
  · have := mul_nonpos_of_nonpos_of_nonneg hC hq0
    linarith
  · push Not at hC
    calc CT * ((D.R.f : ℝ) * D.R.r / ((min (D.host.g 0) (D.host.g 1) : ℕ) : ℝ))
        ≤ CT * (2 / L.sc.b) := mul_le_mul_of_nonneg_left hq hC.le
      _ = 2 * CT / L.sc.b := by ring
      _ ≤ 1 / 3 := by rw [div_le_iff₀ hb0]; linarith

section ParF

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

/- English proof (translation)
Establish `he : 0 < eps`. Take `⟨i⟩` from `Fm.Ix_zero`. Rewrite using `[← Fm.L_eps 0 i]`. Conclude with `(Fm.L 0 i).sc.eps_pos`. Use `⟨(max c 1) ^ (1 / eps), fun x hx h1 i => ?_⟩` and prove the remaining obligations.

Establish `hc1 : (1 : ℝ) ≤ max c 1` using `le_max_right _ _`. Establish `h2 : ((max c 1) ^ (1 / eps)) ^ eps ≤ x ^ eps` using `Real.rpow_le_rpow (by positivity) hx he.le`. Rewrite `h2` using `[← Real.rpow_mul (by linarith), one_div_mul_cancel he.ne', Real.rpow_one]`. Unfold `Scale.b Scale.L`. Rewrite using `[Fm.L_x x i h1, Fm.L_eps x i]`.

Establish `h3` using `Real.add_one_le_exp (x ^ eps)`. Establish `h4 : c ≤ max c 1` using `le_max_left _ _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem b_geF (c : ℝ) : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ _ : Fm.x1 < x, ∀ i : Fm.Ix x, c ≤ (Fm.L x i).sc.b := by
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  refine ⟨(max c 1) ^ (1 / eps), fun x hx h1 i => ?_⟩
  have hc1 : (1 : ℝ) ≤ max c 1 := le_max_right _ _
  have h2 : ((max c 1) ^ (1 / eps)) ^ eps ≤ x ^ eps := Real.rpow_le_rpow (by positivity) hx he.le
  rw [← Real.rpow_mul (by linarith), one_div_mul_cancel he.ne', Real.rpow_one] at h2
  unfold Scale.b Scale.L
  rw [Fm.L_x x i h1, Fm.L_eps x i]
  have h3 := Real.add_one_le_exp (x ^ eps)
  have h4 : c ≤ max c 1 := le_max_left _ _
  linarith

/- English proof (translation)
Take `⟨x0, h0⟩` from `b_geF Fm (6 * CT)`. Conclude with `⟨x0, fun x hx h1 i => delT_of _ _ (Fm.sizes x h1 i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 CT (h0 x hx h1 i)⟩`.
-/
theorem delTF_of (CT : ℝ) : ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ _ : Fm.x1 < x, ∀ i : Fm.Ix x,
    CT * (((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r /
      (min ((Fm.D x i).host.g 0) ((Fm.D x i).host.g 1) : ℕ)) ≤ 1 / 3 := by
  obtain ⟨x0, h0⟩ := b_geF Fm (6 * CT)
  exact ⟨x0, fun x hx h1 i => delT_of _ _
    (Fm.sizes x h1 i).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 CT (h0 x hx h1 i)⟩

end ParF

/- English proof (translation)
Substitute `h` using the available equality. Rewrite using `[Fin.sum_univ_eq_sum_range (fun i => if a ≤ i then c else 0) (a + m), Finset.sum_range_add, Finset.sum_eq_zero (fun i hi => if_neg (by have := Finset.mem_range.1 hi; omega)), zero_add, Finset.sum_congr rfl (fun i _ => if_pos (Nat.le_add_right a i)), Finset.sum_const, Finset.card_ …`.
-/
theorem sum_fin_ite_ge (r a m : ℕ) (h : r = a + m) (c : ℝ) :
    (∑ i : Fin r, (if a ≤ i.val then c else 0)) = m * c := by
  subst h
  rw [Fin.sum_univ_eq_sum_range (fun i => if a ≤ i then c else 0) (a + m), Finset.sum_range_add,
    Finset.sum_eq_zero (fun i hi => if_neg (by have := Finset.mem_range.1 hi; omega)), zero_add,
    Finset.sum_congr rfl (fun i _ => if_pos (Nat.le_add_right a i)), Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/- English proof (translation)
Take `⟨-, -, hcl, hlow, -, hwin, -⟩` from `hSet`. Take `⟨-, -, -, -, -, -, -, -, -, hN, -, -, hkS, -⟩` from `hSz`. Establish `hx0 : 0 < L.sc.x` using `by linarith [L.sc.one_lt_alt]`. Establish `hb0 : 0 < L.sc.b` using `by unfold Scale.b; exact Real.exp_pos _`. Establish `hS0` using `L.Sc_pos`.

Establish `hη0` using `L.etaSz_pos`. Establish `hw0 : 0 ≤ L.sc.w'' D.R.n`. Unfold `Scale.w'' Scale.b' Scale.a Scale.X' Scale.b`. Check the signs of the components of the expression. Establish `hk1 : (1 : ℝ) ≤ D.R.k`.

Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions.

Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Conclude with `this` after adjusting the coercions. Establish `ht1 : (1 : ℝ) ≤ D.R.t`. Establish `: 1 ≤ D.R.t` using `by have := D.R.rank_add_five_le; omega`.

Conclude with `this` after adjusting the coercions. Establish `hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k`. Establish `: D.R.r ≤ 2 * D.R.k` using `by unfold Ranks.r; have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hrt : (D.R.r : ℝ) ≤ D.R.t`.

Establish `: D.R.r ≤ D.R.t` using `by unfold Ranks.r; have := D.R.rank_add_five_le; omega`. Conclude with `this` after adjusting the coercions. Establish `hrkm : (D.R.r : ℝ) ≤ D.R.k + D.R.m`. Establish `: D.R.r ≤ D.R.k + D.R.m` using `by unfold Ranks.r; omega`. Conclude with `this` after adjusting the coercions.

Establish `hr0 : (0 : ℝ) ≤ D.R.r` using `Nat.cast_nonneg _`. Establish `hne : Nonempty D.what₂.Tau` using `Fintype.card_pos_iff.1 (by`. Rewrite using `[D.what₂.card_Tau]`. Unfold `Ranks.f Ranks.n`. Use `D.R.ord_pos` as an intermediate fact.

Use the proof step `omega)`. Take `⟨τ0⟩` from `hne`. Establish `hw2b : L.sc.w'' D.R.n ≤ 2 * L.sc.b` using `(hwin τ0).1.trans (hwin τ0).2`. Establish `hrS : (D.R.r : ℝ) * L.Sc ≤ 4 * L.sc.b`. Establish `: (D.R.r : ℝ) * L.Sc ≤ 2 * D.R.k * L.Sc` using `mul_le_mul_of_nonneg_right hr2k hS0.le`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hP : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 2 * D.R.f * (D.R.k : ℝ) ^ 3`. Establish `h1 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 2` using `one_le_pow₀ ht1`. Establish `h3 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3` using `one_le_pow₀ hk1`. Establish `h4 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 2 * D.R.f` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hηb : (D.R.t : ℝ) * L.etaSz ≤ L.sc.b`. Establish `h1` using `hEta.2.1`. Rewrite `h1` using `[le_div_iff₀ (by positivity)]`. Establish `h2 : (D.R.t : ℝ) * L.etaSz ≤ (D.R.t : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 2 * D.R.f * (D.R.k : ℝ) ^ 3)` using `le_mul_of_one_le_right (by positivity) hP`.

Establish `h3 : (D.R.t : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 2 * D.R.f * (D.R.k : ℝ) ^ 3) = L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3)` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hrη : (D.R.r : ℝ) * L.etaSz ≤ L.sc.b` using `(mul_le_mul_of_nonneg_right hrt hη0.le).trans hηb`. Establish `hηb' : L.etaSz ≤ L.sc.b` using `by nlinarith`. Establish `hNN : (D.R.r : ℝ) * ((D.R.r : ℝ) + D.R.t) ≤ L.sc.b`.

Establish `hNe : placeRankTwoOne.NN D = (D.R.k : ℝ) + D.R.m * ((D.R.t : ℝ) + 1)`. Unfold `placeRankTwoOne.NN Ranks.N`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hN1 : (D.R.r : ℝ) ≤ placeRankTwoOne.NN D` using `by rw [hNe]; nlinarith`.

Establish `hN2 : (D.R.t : ℝ) ≤ placeRankTwoOne.NN D` using `by rw [hNe]; nlinarith`. Establish `hN3 : (1 : ℝ) ≤ placeRankTwoOne.NN D` using `by linarith`. Establish `h1 : (D.R.r : ℝ) * ((D.R.r : ℝ) + D.R.t) ≤ placeRankTwoOne.NN D * (2 * placeRankTwoOne.NN D)` using `mul_le_mul hN1 (by linarith) (by linarith) (by linarith)`. Establish `h2 : placeRankTwoOne.NN D * (2 * placeRankTwoOne.NN D) ≤ 4 * placeRankTwoOne.NN D ^ 3` using `by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ placeRankTwoOne.NN D) (by linarith : (0:ℝ) ≤ placeRankTwoOne.NN D)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `set A : ℝ := L.Sc + L.etaSz + Cn * ((D.R.r : ℝ) + D.R.t) with hA`. Establish `hCRT : 0 ≤ Cn * ((D.R.r : ℝ) + D.R.t)` using `by positivity`. Establish `hrA : (D.R.r : ℝ) * A ≤ (5 + Cn) * L.sc.b`. Establish `: (D.R.r : ℝ) * A = D.R.r * L.Sc + D.R.r * L.etaSz + Cn * ((D.R.r : ℝ) * ((D.R.r : ℝ) + D.R.t))`. Rewrite using `[hA]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h2 : Cn * ((D.R.r : ℝ) * ((D.R.r : ℝ) + D.R.t)) ≤ Cn * L.sc.b` using `mul_le_mul_of_nonneg_left hNN hCn`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hterm : ∀ τ (i : Fin D.R.r), |(DV.kapW D j τ i : ℝ) - w τ| ≤ A + (if D.R.k - 1 ≤ i.val then 2 * L.sc.b else 0)`. Introduce `τ i`.

Distinguish the cases in `h : i.val < D.R.k - 1`. Take `⟨h1, h2⟩` from `hcl τ i h`. Rewrite using `[if_neg (by omega), abs_le]`. Apply the tactic sequence `constructor <;> linarith`. Rewrite using `[if_pos (by omega)]`.

Establish `h1` using `hlow τ i (by omega)`. Establish `hw` using `hwin τ`. Establish `h3 : |((w τ : ℤ) : ℝ)| ≤ 2 * L.sc.b` using `by rw [abs_of_nonneg (by linarith)]; exact hw.2`. Establish `h4` using `abs_sub (DV.kapW D j τ i : ℝ) (w τ : ℝ)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hrk : D.R.r = (D.R.k - 1) + D.R.m`. Unfold `Ranks.r`. Use `D.R.m_add_three_le_k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hin : ∀ τ, (∑ i, |(DV.kapW D j τ i : ℝ) - w τ|) ≤ (5 + Cn) * L.sc.b + D.R.m * (2 * L.sc.b)`.

Introduce `τ`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_add_distrib, sum_fin_ite_ge _ _ _ hrk, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Use `_ ≤ _ := by linarith`. Unfold `placeRankTwoOne.normU`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]`. Use `_ ≤ (7 + Cn) * ((D.R.f : ℝ) * D.R.m * L.sc.b) := by`. Establish `h1 : (5 + Cn) * L.sc.b ≤ (5 + Cn) * L.sc.b * D.R.m` using `le_mul_of_one_le_right (by positivity) hm1`. Establish `h2 : (5 + Cn) * L.sc.b + D.R.m * (2 * L.sc.b) ≤ (7 + Cn) * (D.R.m * L.sc.b)` using `by linarith`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem normU_le_of_Set (D : D7) (L : SizeData₂ D) (Cn CP AP Cq Cs : ℝ) (hCn : 0 ≤ Cn) (j : ℕ)
    (w : D.what₂.Tau → ℤ) (hSet : placeRankTwoOne.SizeSettingLemmaThree D L Cn CP AP Cq j w) (hSz : placeRankTwoOne.Sizes D L Cs)
    (hEta : Formalism.MainNotions.SizeEta L) :
    placeRankTwoOne.normU D j w ≤ (7 + Cn) * ((D.R.f : ℝ) * D.R.m * L.sc.b) := by
  obtain ⟨-, -, hcl, hlow, -, hwin, -⟩ := hSet
  obtain ⟨-, -, -, -, -, -, -, -, -, hN, -, -, hkS, -⟩ := hSz
  have hx0 : 0 < L.sc.x := by linarith [L.sc.one_lt_alt]
  have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have hS0 := L.Sc_pos
  have hη0 := L.etaSz_pos
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.X' Scale.b; positivity
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
    exact_mod_cast this
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by
    have : D.R.r ≤ 2 * D.R.k := by unfold Ranks.r; have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hrt : (D.R.r : ℝ) ≤ D.R.t := by
    have : D.R.r ≤ D.R.t := by unfold Ranks.r; have := D.R.rank_add_five_le; omega
    exact_mod_cast this
  have hrkm : (D.R.r : ℝ) ≤ D.R.k + D.R.m := by
    have : D.R.r ≤ D.R.k + D.R.m := by unfold Ranks.r; omega
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ D.R.r := Nat.cast_nonneg _
  have hne : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by
    rw [D.what₂.card_Tau]; unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega)
  obtain ⟨τ0⟩ := hne
  have hw2b : L.sc.w'' D.R.n ≤ 2 * L.sc.b := (hwin τ0).1.trans (hwin τ0).2

  have hrS : (D.R.r : ℝ) * L.Sc ≤ 4 * L.sc.b := by
    have : (D.R.r : ℝ) * L.Sc ≤ 2 * D.R.k * L.Sc := mul_le_mul_of_nonneg_right hr2k hS0.le
    nlinarith
  have hP : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 2 * D.R.f * (D.R.k : ℝ) ^ 3 := by
    have h1 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 2 := one_le_pow₀ ht1
    have h3 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk1
    have h4 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 2 * D.R.f := by nlinarith
    nlinarith
  have hηb : (D.R.t : ℝ) * L.etaSz ≤ L.sc.b := by
    have h1 := hEta.2.1
    rw [le_div_iff₀ (by positivity)] at h1
    have h2 : (D.R.t : ℝ) * L.etaSz ≤ (D.R.t : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 2 * D.R.f * (D.R.k : ℝ) ^ 3) :=
      le_mul_of_one_le_right (by positivity) hP
    have h3 : (D.R.t : ℝ) * L.etaSz * ((D.R.t : ℝ) ^ 2 * D.R.f * (D.R.k : ℝ) ^ 3) =
        L.etaSz * ((D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3) := by ring
    linarith
  have hrη : (D.R.r : ℝ) * L.etaSz ≤ L.sc.b :=
    (mul_le_mul_of_nonneg_right hrt hη0.le).trans hηb
  have hηb' : L.etaSz ≤ L.sc.b := by nlinarith
  have hNN : (D.R.r : ℝ) * ((D.R.r : ℝ) + D.R.t) ≤ L.sc.b := by
    have hNe : placeRankTwoOne.NN D = (D.R.k : ℝ) + D.R.m * ((D.R.t : ℝ) + 1) := by
      unfold placeRankTwoOne.NN Ranks.N; push_cast; ring
    have hN1 : (D.R.r : ℝ) ≤ placeRankTwoOne.NN D := by rw [hNe]; nlinarith
    have hN2 : (D.R.t : ℝ) ≤ placeRankTwoOne.NN D := by rw [hNe]; nlinarith
    have hN3 : (1 : ℝ) ≤ placeRankTwoOne.NN D := by linarith
    have h1 : (D.R.r : ℝ) * ((D.R.r : ℝ) + D.R.t) ≤ placeRankTwoOne.NN D * (2 * placeRankTwoOne.NN D) :=
      mul_le_mul hN1 (by linarith) (by linarith) (by linarith)
    have h2 : placeRankTwoOne.NN D * (2 * placeRankTwoOne.NN D) ≤ 4 * placeRankTwoOne.NN D ^ 3 := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ placeRankTwoOne.NN D) (by linarith : (0:ℝ) ≤ placeRankTwoOne.NN D)]
    linarith
  set A : ℝ := L.Sc + L.etaSz + Cn * ((D.R.r : ℝ) + D.R.t) with hA
  have hCRT : 0 ≤ Cn * ((D.R.r : ℝ) + D.R.t) := by positivity
  have hrA : (D.R.r : ℝ) * A ≤ (5 + Cn) * L.sc.b := by
    have : (D.R.r : ℝ) * A = D.R.r * L.Sc + D.R.r * L.etaSz + Cn * ((D.R.r : ℝ) * ((D.R.r : ℝ) + D.R.t)) := by
      rw [hA]; ring
    have h2 : Cn * ((D.R.r : ℝ) * ((D.R.r : ℝ) + D.R.t)) ≤ Cn * L.sc.b := mul_le_mul_of_nonneg_left hNN hCn
    linarith
  have hterm : ∀ τ (i : Fin D.R.r), |(DV.kapW D j τ i : ℝ) - w τ| ≤
      A + (if D.R.k - 1 ≤ i.val then 2 * L.sc.b else 0) := by
    intro τ i
    by_cases h : i.val < D.R.k - 1
    · obtain ⟨h1, h2⟩ := hcl τ i h
      rw [if_neg (by omega), abs_le]
      constructor <;> linarith
    · rw [if_pos (by omega)]
      have h1 := hlow τ i (by omega)
      have hw := hwin τ
      have h3 : |((w τ : ℤ) : ℝ)| ≤ 2 * L.sc.b := by rw [abs_of_nonneg (by linarith)]; exact hw.2
      have h4 := abs_sub (DV.kapW D j τ i : ℝ) (w τ : ℝ)
      linarith
  have hrk : D.R.r = (D.R.k - 1) + D.R.m := by
    unfold Ranks.r; have := D.R.m_add_three_le_k; omega
  have hin : ∀ τ, (∑ i, |(DV.kapW D j τ i : ℝ) - w τ|) ≤ (5 + Cn) * L.sc.b + D.R.m * (2 * L.sc.b) := by
    intro τ
    calc (∑ i, |(DV.kapW D j τ i : ℝ) - w τ|)
        ≤ ∑ i : Fin D.R.r, (A + (if D.R.k - 1 ≤ i.val then 2 * L.sc.b else 0)) :=
          Finset.sum_le_sum fun i _ => hterm τ i
      _ = D.R.r * A + D.R.m * (2 * L.sc.b) := by
          rw [Finset.sum_add_distrib, sum_fin_ite_ge _ _ _ hrk, Finset.sum_const, Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := by linarith
  unfold placeRankTwoOne.normU
  calc (∑ τ, ∑ i, |(DV.kapW D j τ i : ℝ) - w τ|)
      ≤ ∑ _τ : D.what₂.Tau, ((5 + Cn) * L.sc.b + D.R.m * (2 * L.sc.b)) := Finset.sum_le_sum fun τ _ => hin τ
    _ = D.R.f * ((5 + Cn) * L.sc.b + D.R.m * (2 * L.sc.b)) := by
        rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul]
    _ ≤ (7 + Cn) * ((D.R.f : ℝ) * D.R.m * L.sc.b) := by
        have h1 : (5 + Cn) * L.sc.b ≤ (5 + Cn) * L.sc.b * D.R.m :=
          le_mul_of_one_le_right (by positivity) hm1
        have h2 : (5 + Cn) * L.sc.b + D.R.m * (2 * L.sc.b) ≤ (7 + Cn) * (D.R.m * L.sc.b) := by linarith
        calc (D.R.f : ℝ) * ((5 + Cn) * L.sc.b + D.R.m * (2 * L.sc.b))
            ≤ D.R.f * ((7 + Cn) * (D.R.m * L.sc.b)) := mul_le_mul_of_nonneg_left h2 (by linarith)
          _ = _ := by ring

/- English proof (translation)
Take `⟨z, hz⟩` from `DV.eQ_int D j τ`. Establish `h : DV.wSz D j τ = (z : ℝ)` using `by rw [← DV.eQ_cast, hz, Rat.cast_intCast]`. Unfold `placeRankTwoOne.wI`. Rewrite using `[h, round_intCast]`.
-/
theorem wI_cast_h (D : D7) (j : ℕ) (τ : D.what₂.Tau) : ((placeRankTwoOne.wI D j τ : ℤ) : ℝ) = DV.wSz D j τ := by
  obtain ⟨z, hz⟩ := DV.eQ_int D j τ
  have h : DV.wSz D j τ = (z : ℝ) := by rw [← DV.eQ_cast, hz, Rat.cast_intCast]
  unfold placeRankTwoOne.wI
  rw [h, round_intCast]

/- English proof (translation)
Introduce `j hj`. Take `⟨hj1, hj2⟩` from `Finset.mem_Icc.1 hj`. Establish `hS` using `hSet j hj1 hj2`. Establish `hU` using `normU_le_of_Set D L Cn CP AP Cq Cs hCn j _ hS hSz hEta`. Take `⟨-, -, -, -, -, hwin, -, -, -, -, -, -, -, -, -, -, -, -, -, hld, -⟩` from `hS`.

Take `⟨-, hrd, hdl, h4x, hll, -⟩` from `hSz`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hb1 : 1 ≤ L.sc.b` using `by unfold Scale.b; exact Real.one_le_exp (by linarith)`.

Establish `hlb : Real.log L.sc.b = L.sc.L` using `by unfold Scale.b; exact Real.log_exp _`. Establish `hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L` using `rfl`. Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions.

Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Conclude with `this` after adjusting the coercions. Establish `hw0 : 0 ≤ L.sc.w'' D.R.n`. Unfold `Scale.w'' Scale.b' Scale.a Scale.X' Scale.b`.

Check the signs of the components of the expression. Establish `hrd1` using `one_le_rdE D`. Establish `hlrd : 0 ≤ Real.log D.host.rdE` using `Real.log_nonneg hrd1`. Establish `hG : 2 * Real.log (placeRankTwoOne.rdK D) - Real.log D.host.rdE ≤ L.sc.L`. Unfold `placeRankTwoOne.rdK`.

Rewrite using `[Real.log_sqrt (Nat.cast_nonneg _)]`. Establish `h1 : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.L`. Unfold `Scale.L`. Conclude with `Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [L.sc.eps_pos])`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq0 : 0 ≤ placeRankTwoOne.qS D j`. Unfold `placeRankTwoOne.qS`. Establish `: (j : ℝ) ≤ D.R.m` using `by exact_mod_cast hj2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hqm : placeRankTwoOne.qS D j ≤ D.R.m`.

Unfold `placeRankTwoOne.qS`. Establish `: (0 : ℝ) ≤ j` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfmb : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b` using `by positivity`. Establish `hbB : L.sc.b ≤ L.B0`.

Rewrite using `[hB0]`. Establish `h1 : L.sc.b ≤ (D.R.f : ℝ) * D.R.m * L.sc.b`. Establish `: (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.m` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `h1.trans (le_mul_of_one_le_right hfmb hL1)`.

Establish `hBnn : 0 ≤ L.B0` using `by linarith`. Establish `hT1 : (∑ τ : D.what₂.Tau, DV.wSz D j τ * (2 * placeRankTwoOne.qS D j * (2 * Real.log (placeRankTwoOne.rdK D) - Real.log D.host.rdE))) ≤ 4 * L.B0`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[← wI_cast_h D j τ]`.

Establish `hw` using `hwin τ`. Establish `h1 : 2 * placeRankTwoOne.qS D j * (2 * Real.log (placeRankTwoOne.rdK D) - Real.log D.host.rdE) ≤ 2 * D.R.m * L.sc.L` using `(mul_le_mul_of_nonneg_left hG (by linarith)).trans (mul_le_mul_of_nonneg_right (by linarith) (by linarith))`. Conclude with `(mul_le_mul_of_nonneg_left h1 (by linarith)).trans (mul_le_mul_of_nonneg_right hw.2 (by positivity))`. Use `_ = 4 * L.B0 := by`. Rewrite using `[Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul, hB0]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hll0 : 0 ≤ Real.log (Real.log L.sc.x)` using `by linarith`. Establish `hlx : Real.log L.sc.x ≤ L.sc.L` using `(Real.log_le_log hx0 (by linarith)).trans h4x`. Establish `hlx0 : 0 ≤ Real.log L.sc.x` using `Real.log_nonneg hx1.le`. Establish `hlbr : Real.log (L.sc.b * D.host.rdE) = L.sc.L + Real.log D.host.rdE`.

Rewrite using `[Real.log_mul (by linarith) (by linarith), hlb]`. Establish `hLL : placeRankTwoOne.LL0 D L ≤ 4 * L.sc.L * Real.log (Real.log L.sc.x)`. Unfold `placeRankTwoOne.LL0`. Rewrite using `[hlbr]`. Establish `h1 : (L.sc.L + Real.log D.host.rdE) * Real.log (Real.log L.sc.x) ≤ 2 * L.sc.L * Real.log (Real.log L.sc.x)` using `mul_le_mul_of_nonneg_right (by linarith) hll0`.

Establish `h2 : L.sc.L ≤ L.sc.L * Real.log (Real.log L.sc.x)` using `le_mul_of_one_le_right (by linarith) hll`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hLL0 : 0 ≤ placeRankTwoOne.LL0 D L`. Unfold `placeRankTwoOne.LL0`. Rewrite using `[hlbr]`.

Use `abs_nonneg L.logDerivativeAtOne` as an intermediate fact. Establish `: 0 ≤ (L.sc.L + Real.log D.host.rdE) * Real.log (Real.log L.sc.x)` using `mul_nonneg (by linarith) hll0`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hU0 : 0 ≤ placeRankTwoOne.normU D j (placeRankTwoOne.wI D j)`. Unfold `placeRankTwoOne.normU`.

Conclude with `Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => abs_nonneg _`. Establish `hprod : placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j) ≤ 4 * L.sc.L * Real.log (Real.log L.sc.x) * ((7 + Cn) * ((D.R.f : ℝ) * D.R.m * L.sc.b))` using `mul_le_mul hLL hU hU0 (by positivity)`. Establish `hT2 : 2 * C6 * placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j) ≤ 8 * max C6 0 * (7 + Cn) * L.B0 * Real.log (Real.log L.sc.x)`. Establish `h0 : 0 ≤ placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j)` using `mul_nonneg hLL0 hU0`. Combine the equalities or inequalities in the displayed calculation.

Establish `hBl : L.B0 ≤ L.B0 * Real.log (Real.log L.sc.x)` using `le_mul_of_one_le_right hBnn hll`. Establish `hfin : (6 + 8 * max C6 0 * (7 + Cn)) * L.B0 * Real.log (Real.log L.sc.x) = 6 * (L.B0 * Real.log (Real.log L.sc.x)) + 8 * max C6 0 * (7 + Cn) * L.B0 * Real.log (Real.log L.sc.x)` using `by ring`. Rewrite using `[hfin]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem SizeL3body_of_Set (D : D7) (L : SizeData₂ D) (Cn CP AP Cq Cs C6 : ℝ) (hCn : 0 ≤ Cn)
    (hSet : ∀ j, 1 ≤ j → j ≤ D.R.m → placeRankTwoOne.SizeSettingLemmaThree D L Cn CP AP Cq j (placeRankTwoOne.wI D j))
    (hSz : placeRankTwoOne.Sizes D L Cs) (hEta : Formalism.MainNotions.SizeEta L) :
    ∀ j ∈ SizeData₂.lifts D,
      (∑ τ : D.what₂.Tau, DV.wSz D j τ *
          (2 * placeRankTwoOne.qS D j * (2 * Real.log (placeRankTwoOne.rdK D) - Real.log D.host.rdE))) +
        2 * C6 * placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j) + 2 * L.sc.b ≤ (6 + 8 * max C6 0 * (7 + Cn)) * L.B0 * Real.log (Real.log L.sc.x) := by
  intro j hj
  obtain ⟨hj1, hj2⟩ := Finset.mem_Icc.1 hj
  have hS := hSet j hj1 hj2
  have hU := normU_le_of_Set D L Cn CP AP Cq Cs hCn j _ hS hSz hEta
  obtain ⟨-, -, -, -, -, hwin, -, -, -, -, -, -, -, -, -, -, -, -, -, hld, -⟩ := hS
  obtain ⟨-, hrd, hdl, h4x, hll, -⟩ := hSz
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  have hlb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hB0 : L.B0 = (D.R.f : ℝ) * D.R.m * L.sc.b * L.sc.L := rfl
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.X' Scale.b; positivity
  have hrd1 := one_le_rdE D
  have hlrd : 0 ≤ Real.log D.host.rdE := Real.log_nonneg hrd1
  have hG : 2 * Real.log (placeRankTwoOne.rdK D) - Real.log D.host.rdE ≤ L.sc.L := by
    unfold placeRankTwoOne.rdK
    rw [Real.log_sqrt (Nat.cast_nonneg _)]
    have h1 : L.sc.x ^ (L.sc.eps / 4) ≤ L.sc.L := by
      unfold Scale.L
      exact Real.rpow_le_rpow_of_exponent_le hx1.le (by linarith [L.sc.eps_pos])
    linarith
  have hq0 : 0 ≤ placeRankTwoOne.qS D j := by
    unfold placeRankTwoOne.qS
    have : (j : ℝ) ≤ D.R.m := by exact_mod_cast hj2
    linarith
  have hqm : placeRankTwoOne.qS D j ≤ D.R.m := by
    unfold placeRankTwoOne.qS
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg _
    linarith
  have hfmb : 0 ≤ (D.R.f : ℝ) * D.R.m * L.sc.b := by positivity
  have hbB : L.sc.b ≤ L.B0 := by
    rw [hB0]
    have h1 : L.sc.b ≤ (D.R.f : ℝ) * D.R.m * L.sc.b := by
      have : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.m := by nlinarith
      nlinarith
    exact h1.trans (le_mul_of_one_le_right hfmb hL1)
  have hBnn : 0 ≤ L.B0 := by linarith

  have hT1 : (∑ τ : D.what₂.Tau, DV.wSz D j τ *
      (2 * placeRankTwoOne.qS D j * (2 * Real.log (placeRankTwoOne.rdK D) - Real.log D.host.rdE))) ≤ 4 * L.B0 := by
    calc _ ≤ ∑ _τ : D.what₂.Tau, 2 * L.sc.b * (2 * D.R.m * L.sc.L) := by
          refine Finset.sum_le_sum fun τ _ => ?_
          rw [← wI_cast_h D j τ]
          have hw := hwin τ
          have h1 : 2 * placeRankTwoOne.qS D j * (2 * Real.log (placeRankTwoOne.rdK D) - Real.log D.host.rdE) ≤
              2 * D.R.m * L.sc.L :=
            (mul_le_mul_of_nonneg_left hG (by linarith)).trans
              (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
          exact (mul_le_mul_of_nonneg_left h1 (by linarith)).trans
            (mul_le_mul_of_nonneg_right hw.2 (by positivity))
      _ = 4 * L.B0 := by
          rw [Finset.sum_const, Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul, hB0]; ring

  have hll0 : 0 ≤ Real.log (Real.log L.sc.x) := by linarith
  have hlx : Real.log L.sc.x ≤ L.sc.L :=
    (Real.log_le_log hx0 (by linarith)).trans h4x
  have hlx0 : 0 ≤ Real.log L.sc.x := Real.log_nonneg hx1.le
  have hlbr : Real.log (L.sc.b * D.host.rdE) = L.sc.L + Real.log D.host.rdE := by
    rw [Real.log_mul (by linarith) (by linarith), hlb]
  have hLL : placeRankTwoOne.LL0 D L ≤ 4 * L.sc.L * Real.log (Real.log L.sc.x) := by
    unfold placeRankTwoOne.LL0
    rw [hlbr]
    have h1 : (L.sc.L + Real.log D.host.rdE) * Real.log (Real.log L.sc.x) ≤
        2 * L.sc.L * Real.log (Real.log L.sc.x) := mul_le_mul_of_nonneg_right (by linarith) hll0
    have h2 : L.sc.L ≤ L.sc.L * Real.log (Real.log L.sc.x) := le_mul_of_one_le_right (by linarith) hll
    linarith
  have hLL0 : 0 ≤ placeRankTwoOne.LL0 D L := by
    unfold placeRankTwoOne.LL0
    rw [hlbr]
    have := abs_nonneg L.logDerivativeAtOne
    have : 0 ≤ (L.sc.L + Real.log D.host.rdE) * Real.log (Real.log L.sc.x) :=
      mul_nonneg (by linarith) hll0
    linarith
  have hU0 : 0 ≤ placeRankTwoOne.normU D j (placeRankTwoOne.wI D j) := by
    unfold placeRankTwoOne.normU
    exact Finset.sum_nonneg fun τ _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  have hprod : placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j) ≤
      4 * L.sc.L * Real.log (Real.log L.sc.x) * ((7 + Cn) * ((D.R.f : ℝ) * D.R.m * L.sc.b)) :=
    mul_le_mul hLL hU hU0 (by positivity)
  have hT2 : 2 * C6 * placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j) ≤
      8 * max C6 0 * (7 + Cn) * L.B0 * Real.log (Real.log L.sc.x) := by
    have h0 : 0 ≤ placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j) := mul_nonneg hLL0 hU0
    calc 2 * C6 * placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j)
        = 2 * C6 * (placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j)) := by ring
      _ ≤ 2 * max C6 0 * (placeRankTwoOne.LL0 D L * placeRankTwoOne.normU D j (placeRankTwoOne.wI D j)) :=
          mul_le_mul_of_nonneg_right (by linarith [le_max_left C6 0]) h0
      _ ≤ 2 * max C6 0 * (4 * L.sc.L * Real.log (Real.log L.sc.x) *
            ((7 + Cn) * ((D.R.f : ℝ) * D.R.m * L.sc.b))) :=
          mul_le_mul_of_nonneg_left hprod (by linarith [le_max_right C6 0])
      _ = _ := by rw [hB0]; ring
  have hBl : L.B0 ≤ L.B0 * Real.log (Real.log L.sc.x) := le_mul_of_one_le_right hBnn hll
  have hfin : (6 + 8 * max C6 0 * (7 + Cn)) * L.B0 * Real.log (Real.log L.sc.x) =
      6 * (L.B0 * Real.log (Real.log L.sc.x)) +
        8 * max C6 0 * (7 + Cn) * L.B0 * Real.log (Real.log L.sc.x) := by ring
  rw [hfin]
  linarith

section L3F

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

/- English proof (translation)
Take `⟨y, -, h1, -, ⟨i⟩⟩` from `Fm.exists_pt 0`. Take `⟨Y, hY1, -, hY3, -⟩` from `(Fm.params _ h1 i).g_Y`. Rewrite `hY3` using `[Fm.params_CYL _ h1 i]`. Establish `hx1` using `(Fm.L _ i).sc.one_lt_alt`. Establish `hL1 : 1 ≤ (Fm.L _ i).sc.L`.

Unfold `Scale.L`. Conclude with `Real.one_le_rpow hx1.le (Fm.L _ i).sc.eps_pos.le`. Establish `hb1 : 1 ≤ (Fm.L _ i).sc.b` using `by unfold Scale.b; exact Real.one_le_exp (by linarith)`. Establish `hk1 : (1 : ℝ) ≤ (Fm.D _ i).R.k`. Establish `: 1 ≤ (Fm.D _ i).R.k` using `by have := (Fm.D _ i).R.m_add_three_le_k; omega`.

Conclude with `this` after adjusting the coercions. Establish `hY : 1 ≤ Y` using `le_trans (one_le_pow₀ (by nlinarith)) hY1`. Establish `h0` using `Real.log_nonneg hY`. Assume the negation of the conclusion as `hneg`. Use `push Not at hneg`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem CYL_nonneg : 0 ≤ Fm.CYL := by
  obtain ⟨y, -, h1, -, ⟨i⟩⟩ := Fm.exists_pt 0
  obtain ⟨Y, hY1, -, hY3, -⟩ := (Fm.params _ h1 i).g_Y
  rw [Fm.params_CYL _ h1 i] at hY3
  have hx1 := (Fm.L _ i).sc.one_lt_alt
  have hL1 : 1 ≤ (Fm.L _ i).sc.L := by
    unfold Scale.L; exact Real.one_le_rpow hx1.le (Fm.L _ i).sc.eps_pos.le
  have hb1 : 1 ≤ (Fm.L _ i).sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  have hk1 : (1 : ℝ) ≤ (Fm.D _ i).R.k := by
    have : 1 ≤ (Fm.D _ i).R.k := by have := (Fm.D _ i).R.m_add_three_le_k; omega
    exact_mod_cast this
  have hY : 1 ≤ Y := le_trans (one_le_pow₀ (by nlinarith)) hY1
  have h0 := Real.log_nonneg hY
  by_contra hneg
  push Not at hneg
  nlinarith

/- English proof (translation)
Take `⟨xa, ha⟩` from `hSet`. Take `⟨xb, hb⟩` from `sizes_family_eventually Fm hTu`. Use `⟨max xa xb, fun x hx h1 i => ?_⟩` and prove the remaining obligations. Conclude with `SizeL3body_of_Set _ _ Cn CP AP Cq _ C6 hCn (ha x (le_trans (le_max_left _ _) hx) i (Fm.ex x h1 i).kap_def) (hb x (le_trans (le_max_right _ _) hx) h1 i) (Fm.sizes x h1 i).2.2.2.2.2.2.2.2.2.2.2.2.2.1`.
-/
theorem SizeL3bodyF_of (Cn CP AP Cq C6 : ℝ) (hCn : 0 ≤ Cn) (hSet : placeRankTwoOne.SlopeSettingFamily Fm Cn CP AP Cq)
    (hTu : Formalism.MainNotions.TuSize Fm) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ _ : Fm.x1 < x, ∀ i : Fm.Ix x,
      ∀ j ∈ SizeData₂.lifts (Fm.D x i),
        (∑ τ : (Fm.D x i).what₂.Tau, DV.wSz (Fm.D x i) j τ *
            (2 * placeRankTwoOne.qS (Fm.D x i) j * (2 * Real.log (placeRankTwoOne.rdK (Fm.D x i)) - Real.log (Fm.D x i).host.rdE))) +
          2 * C6 * placeRankTwoOne.LL0 (Fm.D x i) (Fm.L x i) * placeRankTwoOne.normU (Fm.D x i) j (placeRankTwoOne.wI (Fm.D x i) j) +
            2 * (Fm.L x i).sc.b ≤
          (6 + 8 * max C6 0 * (7 + Cn)) * (Fm.L x i).B0 * Real.log (Real.log (Fm.L x i).sc.x) := by
  obtain ⟨xa, ha⟩ := hSet
  obtain ⟨xb, hb⟩ := sizes_family_eventually Fm hTu
  refine ⟨max xa xb, fun x hx h1 i => ?_⟩
  exact SizeL3body_of_Set _ _ Cn CP AP Cq _ C6 hCn
    (ha x (le_trans (le_max_left _ _) hx) i (Fm.ex x h1 i).kap_def)
    (hb x (le_trans (le_max_right _ _) hx) h1 i)
    (Fm.sizes x h1 i).2.2.2.2.2.2.2.2.2.2.2.2.2.1

end L3F

/- English proof (translation)
The claim follows from `|L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps ∧ L.sc.x ^ Cq < (D.host.q : ℝ) ∧ L.sc.x ^ Cq < (D.host.d : ℝ) ∧ Real.log D.host.q ≤ L.sc.x ^ (L.sc.eps / 4) ∧ Real.log D.host.d ≤ L.sc.x ^ (L.sc.eps / 4) ∧ (∀ i, D.host.g i % LevelStarExponents.condE D = 1 ∧ ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ …`.
-/
theorem size_tail_bounds_of (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (hS : Formalism.MainNotions.SizesAt L) (Cn Cq : ℝ)
    (hCn : P.CYL + 1 ≤ Cn) (hCq : Cq ≤ 2 * L.Ct + 5) :
    |L.logDerivativeAtOne| ≤ L.sc.x ^ L.sc.eps ∧
    L.sc.x ^ Cq < (D.host.q : ℝ) ∧ L.sc.x ^ Cq < (D.host.d : ℝ) ∧
    Real.log D.host.q ≤ L.sc.x ^ (L.sc.eps / 4) ∧ Real.log D.host.d ≤ L.sc.x ^ (L.sc.eps / 4) ∧
    (∀ i, D.host.g i % LevelStarExponents.condE D = 1 ∧ ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧
      Real.log (D.host.g i) ≤ Cn * L.sc.L) := by
  obtain ⟨-, -, -, -, -, -, hQD, -⟩ := hS
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hpow : L.sc.x ^ Cq ≤ L.sc.x ^ (2 * L.Ct + 5) := Real.rpow_le_rpow_of_exponent_le hx1.le hCq
  have hexp : L.sc.x ^ (L.sc.eps / 5 + Formalism.MainNotions.szTh L) ≤ L.sc.x ^ (L.sc.eps / 4) := by
    apply Real.rpow_le_rpow_of_exponent_le hx1.le
    unfold Formalism.MainNotions.szTh
    linarith [L.sc.eps_pos]
  refine ⟨P.logDerivative_le_power, lt_of_le_of_lt hpow P.qd_pow.1, lt_of_le_of_lt hpow P.qd_pow.2,
    hQD.2.2.1.trans hexp, hQD.2.2.2.2.1.trans hexp, fun i => ?_⟩
  obtain ⟨Y, hY1, -, hY3, hY4⟩ := P.g_Y
  have hk0 : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have hY0 : 0 < Y := lt_of_lt_of_le (by positivity) hY1
  have hg0 : (0 : ℝ) < D.host.g i := lt_of_lt_of_le hY0 (hY4 i).1
  refine ⟨P.g_mod i, hY1.trans (hY4 i).1, ?_⟩
  have h1 := Real.log_le_log hg0 (hY4 i).2
  rw [Real.log_mul (by norm_num) hY0.ne'] at h1
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num); linarith
  have h3 : (P.CYL + 1) * L.sc.L ≤ Cn * L.sc.L := mul_le_mul_of_nonneg_right hCn (by linarith)
  nlinarith

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hb1 : 1 ≤ L.sc.b` using `by unfold Scale.b; exact Real.one_le_exp (by linarith)`. Establish `hlb : 0 ≤ Real.log L.sc.b` using `Real.log_nonneg hb1`.

Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`.

Conclude with `this` after adjusting the coercions. Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Conclude with `this` after adjusting the coercions. Establish `hr2 : 2 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`.

Establish `hr1 : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast (by omega : 1 ≤ D.R.r)`. Establish `hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ)`. Establish `: D.R.r ≤ D.R.N D.R.m`. Unfold `Ranks.r Ranks.N`. Establish `h1 : D.R.m ≤ D.R.m * (D.R.t + 1)` using `Nat.le_mul_of_pos_right _ (Nat.succ_pos _)`.

Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Establish `hDe : (placeRankTwoOne.dimY D : ℝ) = (T.Dp : ℝ)`. Establish `: placeRankTwoOne.dimY D = T.Dp` using `by rw [T.Dp_eq]; rfl`. Conclude with `this` after adjusting the coercions.

Establish `hD1 : (1 : ℝ) ≤ (T.Dp : ℝ)`. Establish `: 1 ≤ T.Dp`. Rewrite using `[T.Dp_eq]`. Establish `h1 : 0 < D.R.r.choose 2` using `Nat.choose_pos hr2`. Establish `h2 : 0 < D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`.

Conclude with `Nat.mul_pos h2 h1`. Conclude with `this` after adjusting the coercions. Establish `hZ1 : (1 : ℝ) ≤ zBase L`. Unfold `zBase`. Establish `: (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hP1 : 1 ≤ T.PP`. Rewrite using `[T.PP_eq]`. Establish `h1` using `Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)`. Establish `h2` using `T.one_le_CP`.

Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[hDe]`. Use `set p : ℝ := placeRankTwoOne.PP D L CP AP with hp`. Establish `hxCp : 1 ≤ L.sc.x ^ T.Cp` using `Real.one_le_rpow hx1.le T.Cp_nonneg`. Establish `hTTr : placeRankTwoOne.PP D L CP AP ^ 2 * (placeRankTwoOne.dimY D : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) = p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)` using `by rw [hDe]`.

Establish `hT0 : 0 ≤ placeRankTwoOne.TT D L CP AP` using `placeRankTwoOne.TT_nonneg D L CP AP`. Establish `hTO : placeRankTwoOne.TT D L CP AP ≤ (T.TO : ℝ)`. Use `placeRankTwoOne.TT_le_nat D L CP AP T.TO ?_` and prove the remaining obligations. Use `le_trans ?_ T.TO_ge` and prove the remaining obligations. Rewrite using `[hTTr]`.

Establish `a1 : p ^ 2 ≤ T.PP ^ 4` using `(pow_le_pow_left₀ h0 hPP 2).trans (pow_le_pow_right₀ hP1 (by norm_num))`. Establish `a2 : (T.Dp : ℝ) ^ 2 ≤ (T.Dp : ℝ) ^ 3` using `pow_le_pow_right₀ hD1 (by norm_num)`. Establish `a3 : p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k` using `by gcongr`. Establish `a4 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f` using `le_mul_of_one_le_right (by positivity) hf1`. Establish `a5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp` using `le_mul_of_one_le_right (by positivity) hxCp`.

Establish `hd : (D.R.m : ℝ) * L.de2 ≤ D.R.m`. Use `L.thickDensity_le_one` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Conclude with `div_le_div₀ (by positivity) (a3.trans (a4.trans a5)) (mul_pos (by linarith) L.thickDensity_pos) hd`. Establish `hTO0 : (0 : ℝ) ≤ (T.TO : ℝ)` using `Nat.cast_nonneg _`.

Establish `c13 : p ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤ L.sc.b`. Use `le_trans ?_ T.b_ge` and prove the remaining obligations. Establish `e1 : p ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤ T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3` using `by gcongr`. Establish `e2 : T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤ T.CbN * (T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3)` using `le_mul_of_one_le_left (by positivity) T.CbN_ge`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨?_, ?_, c13, ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : placeRankTwoOne.TT D L CP AP ^ 2 ≤ (T.TO : ℝ) ^ 2` using `pow_le_pow_left₀ hT0 hTO 2`. Establish `h2` using `T.heightBound_ge_order_sq`. Establish `h3 : (0 : ℝ) ≤ D.R.t` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `le_trans ?_ T.heightBound_ge_order_product` and prove the remaining obligations. Establish `e1 : p * placeRankTwoOne.TT D L CP AP * (D.R.r : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤ T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ)` using `by gcongr`. Establish `e2 : T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤ T.ChT * (T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ))` using `le_mul_of_one_le_left (by positivity) T.ChT_ge`. Combine the equalities or inequalities in the displayed calculation. Use `le_trans ?_ T.log_bound_le_sqrt` and prove the remaining obligations.

Establish `hpx : p ≤ L.sc.x ^ T.Cb` using `hPP.trans (T.PP_poly.trans (Real.rpow_le_rpow_of_exponent_le hx1.le hCb))`. Establish `e1 : p * placeRankTwoOne.TT D L CP AP * (T.Dp : ℝ) ^ 2 * Real.log L.sc.b ≤ L.sc.x ^ T.Cb * (T.TO : ℝ) * (T.Dp : ℝ) ^ 2 * Real.log L.sc.b` using `by gcongr`. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : p ^ 2 ≤ L.sc.b`. Use `le_trans ?_ c13` and prove the remaining obligations.

Establish `q1 : (1 : ℝ) ≤ (T.Dp : ℝ) ^ 3` using `one_le_pow₀ hD1`. Establish `q0 : 0 ≤ p ^ 2` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Establish `h2 : p ≤ Real.sqrt L.sc.b`. Use `Real.sqrt_le_sqrt h1` as an intermediate fact.

Rewrite `this` using `[Real.sqrt_sq h0]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation.
-/
theorem size_parameter_bounds_of (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) (CP AP : ℝ)
    (h0 : 0 ≤ placeRankTwoOne.PP D L CP AP) (hPP : placeRankTwoOne.PP D L CP AP ≤ T.PP) (hCb : L.Ct ≤ T.Cb) :
    4 * placeRankTwoOne.TT D L CP AP ^ 2 ≤ LevelStarExponents.h0 L ∧
    placeRankTwoOne.PP D L CP AP * placeRankTwoOne.TT D L CP AP * (D.R.r : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * placeRankTwoOne.dimY D
      ≤ LevelStarExponents.h0 L ∧
    placeRankTwoOne.PP D L CP AP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (placeRankTwoOne.dimY D : ℝ) ^ 3 ≤ L.sc.b ∧
    placeRankTwoOne.PP D L CP AP * placeRankTwoOne.TT D L CP AP * (placeRankTwoOne.dimY D : ℝ) ^ 2 * Real.log L.sc.b ≤ L.sc.b ∧
    placeRankTwoOne.PP D L CP AP * Real.sqrt L.sc.b ≤ L.sc.b := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  have hlb : 0 ≤ Real.log L.sc.b := Real.log_nonneg hb1
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.r ≤ D.R.N D.R.m := by
      unfold Ranks.r Ranks.N
      have h1 : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    exact_mod_cast this
  have hDe : (placeRankTwoOne.dimY D : ℝ) = (T.Dp : ℝ) := by
    have : placeRankTwoOne.dimY D = T.Dp := by rw [T.Dp_eq]; rfl
    exact_mod_cast this
  have hD1 : (1 : ℝ) ≤ (T.Dp : ℝ) := by
    have : 1 ≤ T.Dp := by
      rw [T.Dp_eq]
      have h1 : 0 < D.R.r.choose 2 := Nat.choose_pos hr2
      have h2 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
      exact Nat.mul_pos h2 h1
    exact_mod_cast this
  have hZ1 : (1 : ℝ) ≤ zBase L := by
    unfold zBase
    have : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    nlinarith
  have hP1 : 1 ≤ T.PP := by
    rw [T.PP_eq]
    have h1 := Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)
    have h2 := T.one_le_CP
    nlinarith
  rw [hDe]
  set p : ℝ := placeRankTwoOne.PP D L CP AP with hp
  have hxCp : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow hx1.le T.Cp_nonneg
  have hTTr : placeRankTwoOne.PP D L CP AP ^ 2 * (placeRankTwoOne.dimY D : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) =
      p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by rw [hDe]
  have hT0 : 0 ≤ placeRankTwoOne.TT D L CP AP := placeRankTwoOne.TT_nonneg D L CP AP
  have hTO : placeRankTwoOne.TT D L CP AP ≤ (T.TO : ℝ) := by
    refine placeRankTwoOne.TT_le_nat D L CP AP T.TO ?_
    refine le_trans ?_ T.TO_ge
    rw [hTTr]
    have a1 : p ^ 2 ≤ T.PP ^ 4 :=
      (pow_le_pow_left₀ h0 hPP 2).trans (pow_le_pow_right₀ hP1 (by norm_num))
    have a2 : (T.Dp : ℝ) ^ 2 ≤ (T.Dp : ℝ) ^ 3 := pow_le_pow_right₀ hD1 (by norm_num)
    have a3 : p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k := by gcongr
    have a4 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f :=
      le_mul_of_one_le_right (by positivity) hf1
    have a5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤
        T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp :=
      le_mul_of_one_le_right (by positivity) hxCp
    have hd : (D.R.m : ℝ) * L.de2 ≤ D.R.m := by
      have := L.thickDensity_le_one; nlinarith
    exact div_le_div₀ (by positivity) (a3.trans (a4.trans a5)) (mul_pos (by linarith) L.thickDensity_pos) hd
  have hTO0 : (0 : ℝ) ≤ (T.TO : ℝ) := Nat.cast_nonneg _
  have c13 : p ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤ L.sc.b := by
    refine le_trans ?_ T.b_ge
    have e1 : p ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤
        T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 := by gcongr
    have e2 : T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3 ≤
        T.CbN * (T.PP ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k * (T.Dp : ℝ) ^ 3) :=
      le_mul_of_one_le_left (by positivity) T.CbN_ge
    calc _ ≤ _ := e1.trans e2
      _ = _ := by ring
  refine ⟨?_, ?_, c13, ?_, ?_⟩
  · have h1 : placeRankTwoOne.TT D L CP AP ^ 2 ≤ (T.TO : ℝ) ^ 2 := pow_le_pow_left₀ hT0 hTO 2
    have h2 := T.heightBound_ge_order_sq
    have h3 : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  · refine le_trans ?_ T.heightBound_ge_order_product
    have e1 : p * placeRankTwoOne.TT D L CP AP * (D.R.r : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) := by
      gcongr
    have e2 : T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k * (T.Dp : ℝ) ≤
        T.ChT * (T.PP * (T.TO : ℝ) * (D.R.N D.R.m : ℝ) * (D.R.f : ℝ) ^ 2 * (D.R.m : ℝ) ^ 2 * D.R.k *
          (T.Dp : ℝ)) := le_mul_of_one_le_left (by positivity) T.ChT_ge
    calc _ ≤ _ := e1.trans e2
      _ = _ := by ring
  · refine le_trans ?_ T.log_bound_le_sqrt
    have hpx : p ≤ L.sc.x ^ T.Cb :=
      hPP.trans (T.PP_poly.trans (Real.rpow_le_rpow_of_exponent_le hx1.le hCb))
    have e1 : p * placeRankTwoOne.TT D L CP AP * (T.Dp : ℝ) ^ 2 * Real.log L.sc.b ≤
        L.sc.x ^ T.Cb * (T.TO : ℝ) * (T.Dp : ℝ) ^ 2 * Real.log L.sc.b := by gcongr
    calc _ ≤ _ := e1
      _ = _ := by ring
  · have h1 : p ^ 2 ≤ L.sc.b := by
      refine le_trans ?_ c13
      have q1 : (1 : ℝ) ≤ (T.Dp : ℝ) ^ 3 := one_le_pow₀ hD1
      have q0 : 0 ≤ p ^ 2 := by positivity
      calc p ^ 2 ≤ p ^ 2 * (D.R.r : ℝ) := le_mul_of_one_le_right q0 hr1
        _ ≤ p ^ 2 * (D.R.r : ℝ) * D.R.m := le_mul_of_one_le_right (by positivity) hm1
        _ ≤ p ^ 2 * (D.R.r : ℝ) * D.R.m * D.R.k := le_mul_of_one_le_right (by positivity) hk1
        _ ≤ _ := le_mul_of_one_le_right (by positivity) q1
    have h2 : p ≤ Real.sqrt L.sc.b := by
      have := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq h0] at this
    calc p * Real.sqrt L.sc.b ≤ Real.sqrt L.sc.b * Real.sqrt L.sc.b :=
          mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
      _ = L.sc.b := Real.mul_self_sqrt (by linarith)

/- English proof (translation)
Establish `h2` using `two_le_rdE D hq hd`. Establish `h1` using `one_le_absDiscr D`. Establish `hn : (1 : ℝ) ≤ (Module.finrank ℚ D.host.E : ℝ)`. Establish `: 0 < Module.finrank ℚ D.host.E` using `Module.finrank_pos`. Conclude with `this` after adjusting the coercions.

Establish `hle : D.host.rdE ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)|`. Unfold `Host.rdE`. Combine the equalities or inequalities in the displayed calculation. Unfold `logdE`. Establish `h3` using `Real.log_le_log (by norm_num : (0 : ℝ) < 2) (h2.trans hle)`.

Establish `h4` using `Real.log_two_gt_d9`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem half_le_logdE (D : D7) (hq : 2 ≤ D.host.q) (hd : 2 ≤ D.host.d) : 1 / 2 ≤ logdE D := by
  have h2 := two_le_rdE D hq hd
  have h1 := one_le_absDiscr D
  have hn : (1 : ℝ) ≤ (Module.finrank ℚ D.host.E : ℝ) := by
    have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    exact_mod_cast this
  have hle : D.host.rdE ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)| := by
    unfold Host.rdE
    calc _ ≤ |((NumberField.discr D.host.E : ℤ) : ℝ)| ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by rw [div_le_one (by linarith)]; exact hn)
      _ = _ := Real.rpow_one _
  unfold logdE
  have h3 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (h2.trans hle)
  have h4 := Real.log_two_gt_d9
  linarith

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hq2 : 2 ≤ D.host.q` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)`. Establish `hd2 : 2 ≤ D.host.d` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)`.

Establish `hq' : (2 : ℝ) ≤ D.host.q` using `by exact_mod_cast hq2`. Establish `hd' : (2 : ℝ) ≤ D.host.d` using `by exact_mod_cast hd2`. Establish `hrd2` using `two_le_rdE D hq2 hd2`. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`.

Conclude with `this` after adjusting the coercions. Establish `ht1 : (1 : ℝ) ≤ D.R.t`. Establish `: 1 ≤ D.R.t` using `by have := D.R.rank_add_five_le; omega`. Conclude with `this` after adjusting the coercions. Establish `hb1 : 1 ≤ L.sc.b` using `by unfold Scale.b; exact Real.one_le_exp (by linarith)`.

Establish `hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d` using `by nlinarith`. Establish `hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`. Establish `hc : D.host.rdE ≤ Formalism.MainNotions.szCond L`. Use `hQD.2.2.2.2.2.2.2.trans ?_` and prove the remaining obligations. Unfold `Formalism.MainNotions.szCond`.

Establish `: (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d)` using `mul_le_mul_of_nonneg_left hs (by positivity)`. Establish `h0 : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hc1 : 1 ≤ Formalism.MainNotions.szCond L` using `by linarith`. Establish `h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36` using `le_self_pow₀ hc1 (by norm_num)`.

Establish `h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150` using `le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)`. Establish `hsb : Real.sqrt L.sc.b ≤ L.sc.b` using `Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩`. Establish `hfin : D.host.rdE ≤ L.sc.b` using `hc.trans (h36.trans (h150.trans (hCond.trans hsb)))`. Use `Real.log_le_log (by linarith) hfin` as an intermediate fact. Rewrite `this` using `[show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _]`. Then use the resulting hypothesis.
-/
theorem log_rdE_le_L (D : D7) (L : SizeData₂ D) (hCond : Formalism.MainNotions.SizeCond L) (hQD : Formalism.MainNotions.SizeQD L) :
    Real.log D.host.rdE ≤ L.sc.L := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hq2 : 2 ≤ D.host.q := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 : 2 ≤ D.host.d := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
  have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
  have hrd2 := two_le_rdE D hq2 hd2
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have ht1 : (1 : ℝ) ≤ D.R.t := by
    have : 1 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
    exact_mod_cast this
  have hb1 : 1 ≤ L.sc.b := by unfold Scale.b; exact Real.one_le_exp (by linarith)
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d :=
    Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hc : D.host.rdE ≤ Formalism.MainNotions.szCond L := by
    refine hQD.2.2.2.2.2.2.2.trans ?_
    unfold Formalism.MainNotions.szCond
    have : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) / 2 * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hs (by positivity)
    have h0 : (0 : ℝ) ≤ (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := by positivity
    nlinarith
  have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by linarith
  have h36 : Formalism.MainNotions.szCond L ≤ Formalism.MainNotions.szCond L ^ 36 := le_self_pow₀ hc1 (by norm_num)
  have h150 : Formalism.MainNotions.szCond L ^ 36 ≤ Formalism.MainNotions.szCond L ^ 36 * (D.R.t : ℝ) ^ 150 :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht1)
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hfin : D.host.rdE ≤ L.sc.b := hc.trans (h36.trans (h150.trans (hCond.trans hsb)))
  have := Real.log_le_log (by linarith) hfin
  rwa [show Real.log L.sc.b = L.sc.L by unfold Scale.b; exact Real.log_exp _] at this

/- English proof (translation)
Establish `h1` using `one_le_absDiscr D`. Establish `hfr : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ)`. Rewrite using `[D.host.finrank_cmField]`. Unfold `Ranks.f Ranks.n`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hf : (0 : ℝ) < 2 * (D.R.f : ℝ)`. Rewrite using `[← hfr]`. Conclude with `Module.finrank_pos` after adjusting the coercions. Unfold `logdE Host.rdE`.

Rewrite using `[Real.log_rpow (by linarith), hfr]`. Establish `hf' : (D.R.f : ℝ) ≠ 0` using `by intro h0; rw [h0] at hf; simp at hf`. Clear the denominators using the available nonvanishing facts.
-/
theorem logdE_eq (D : D7) : logdE D = 2 * (D.R.f : ℝ) * Real.log D.host.rdE := by
  have h1 := one_le_absDiscr D
  have hfr : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  have hf : (0 : ℝ) < 2 * (D.R.f : ℝ) := by
    rw [← hfr]; exact_mod_cast Module.finrank_pos
  unfold logdE Host.rdE
  rw [Real.log_rpow (by linarith), hfr]
  have hf' : (D.R.f : ℝ) ≠ 0 := by intro h0; rw [h0] at hf; simp at hf
  field_simp

/- English proof (translation)
Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le`. Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Conclude with `this` after adjusting the coercions. Establish `hr1 : (1 : ℝ) ≤ D.R.r`.

Establish `: 1 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hfL : (1 : ℝ) ≤ (D.R.f : ℝ) * L.sc.L` using `by nlinarith`. Establish `hz : (D.R.f : ℝ) * L.sc.L ≤ zBase L`. Unfold `zBase`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hz1 : 1 ≤ zBase L` using `le_trans hfL hz`. Establish `hz2 : zBase L ≤ zBase L ^ 2` using `le_self_pow₀ hz1 (by norm_num)`. Rewrite using `[logdE_eq]`. Establish `: (D.R.f : ℝ) * Real.log D.host.rdE ≤ (D.R.f : ℝ) * L.sc.L` using `mul_le_mul_of_nonneg_left hrd (by linarith)`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem logdE_le_of (D : D7) (L : SizeData₂ D) (hrd : Real.log D.host.rdE ≤ L.sc.L) : logdE D ≤ 2 * zBase L ^ 2 := by
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hfL : (1 : ℝ) ≤ (D.R.f : ℝ) * L.sc.L := by nlinarith
  have hz : (D.R.f : ℝ) * L.sc.L ≤ zBase L := by
    unfold zBase
    nlinarith
  have hz1 : 1 ≤ zBase L := le_trans hfL hz
  have hz2 : zBase L ≤ zBase L ^ 2 := le_self_pow₀ hz1 (by norm_num)
  rw [logdE_eq]
  have : (D.R.f : ℝ) * Real.log D.host.rdE ≤ (D.R.f : ℝ) * L.sc.L := mul_le_mul_of_nonneg_left hrd (by linarith)
  nlinarith

/- English proof (translation)
The claim follows from `logdE_le_of D L (log_rdE_le_L D L hS.2.2.2.2.2.1 hS.2.2.2.2.2.2.1)`.
-/
theorem log_discriminant_le_square_size (D : D7) (L : SizeData₂ D) (hS : Formalism.MainNotions.SizesAt L) : logdE D ≤ 2 * zBase L ^ 2 :=
  logdE_le_of D L (log_rdE_le_L D L hS.2.2.2.2.2.1 hS.2.2.2.2.2.2.1)

/- English proof (translation)
The claim follows from `log_discriminant_le_square_size _ _ (Fm.sizes x hx i)`.
-/
theorem log_discriminant_le_square_size_family {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    logdE (Fm.D x i) ≤ 2 * zBase (Fm.L x i) ^ 2 := log_discriminant_le_square_size _ _ (Fm.sizes x hx i)

/- English proof (translation)
Establish `hS` using `Fm.sizes x hx i`. Establish `hQD` using `hS.2.2.2.2.2.2.1`. Establish `hx0 : 0 < (Fm.L x i).sc.x` using `by linarith [(Fm.L x i).sc.one_lt_alt]`. Establish `hq2` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)`. Establish `hd2` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)`.

Use `⟨size_parameter_bounds_of _ _ (Fm.params x hx i) (Fm.parT x hx i) CP AP ?_ ?_ ?_, size_tail_bounds_of _ _ (Fm.params x hx i) hS _ Cq ?_ ?_⟩` and prove the remaining obligations. Unfold `placeRankTwoOne.PP`. Use `mul_nonneg hCP (Real.rpow_nonneg ?_ _)` and prove the remaining obligations. Establish `h1 : 0 ≤ (Fm.L x i).sc.L` using `by unfold Scale.L; exact (Real.rpow_pos_of_pos hx0 _).le`. Establish `h2` using `Real.log_nonneg (one_le_absDiscr (Fm.D x i))`.

Check the signs of the components of the expression. Conclude with `hPP x hx i`. Rewrite using `[Fm.Ct_eq x i, Fm.parT_Cb x hx i]`. Conclude with `hCb`. Rewrite using `[Fm.params_CYL x hx i]`.

Rewrite using `[Fm.Ct_eq x i]`. Conclude with `hCq`.
-/
theorem size_parameter_bounds_family_of {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (CP AP Cq : ℝ) (hCP : 0 ≤ CP)
    (hPP : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), placeRankTwoOne.PP (Fm.D x i) (Fm.L x i) CP AP ≤ (Fm.parT x hx i).PP) (hCq : Cq ≤ 2 * Fm.Ct + 5) (hCb : Fm.Ct ≤ Fm.Cb)
    (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) :
    (4 * placeRankTwoOne.TT (Fm.D x i) (Fm.L x i) CP AP ^ 2 ≤ LevelStarExponents.h0 (Fm.L x i) ∧
    placeRankTwoOne.PP (Fm.D x i) (Fm.L x i) CP AP * placeRankTwoOne.TT (Fm.D x i) (Fm.L x i) CP AP * ((Fm.D x i).R.r : ℝ) *
      ((Fm.D x i).R.f : ℝ) ^ 2 * ((Fm.D x i).R.m : ℝ) ^ 2 * (Fm.D x i).R.k * placeRankTwoOne.dimY (Fm.D x i)
      ≤ LevelStarExponents.h0 (Fm.L x i) ∧
    placeRankTwoOne.PP (Fm.D x i) (Fm.L x i) CP AP ^ 2 * ((Fm.D x i).R.r : ℝ) * (Fm.D x i).R.m * (Fm.D x i).R.k *
      (placeRankTwoOne.dimY (Fm.D x i) : ℝ) ^ 3 ≤ (Fm.L x i).sc.b ∧
    placeRankTwoOne.PP (Fm.D x i) (Fm.L x i) CP AP * placeRankTwoOne.TT (Fm.D x i) (Fm.L x i) CP AP *
      (placeRankTwoOne.dimY (Fm.D x i) : ℝ) ^ 2 * Real.log (Fm.L x i).sc.b ≤ (Fm.L x i).sc.b ∧
    placeRankTwoOne.PP (Fm.D x i) (Fm.L x i) CP AP * Real.sqrt (Fm.L x i).sc.b ≤ (Fm.L x i).sc.b) ∧
    (|(Fm.L x i).logDerivativeAtOne| ≤ (Fm.L x i).sc.x ^ (Fm.L x i).sc.eps ∧
    (Fm.L x i).sc.x ^ Cq < ((Fm.D x i).host.q : ℝ) ∧ (Fm.L x i).sc.x ^ Cq < ((Fm.D x i).host.d : ℝ) ∧
    Real.log (Fm.D x i).host.q ≤ (Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 4) ∧
    Real.log (Fm.D x i).host.d ≤ (Fm.L x i).sc.x ^ ((Fm.L x i).sc.eps / 4) ∧
    (∀ l, (Fm.D x i).host.g l % LevelStarExponents.condE (Fm.D x i) = 1 ∧
      (((Fm.D x i).R.k : ℝ) * (Fm.L x i).sc.b) ^ 8 ≤ ((Fm.D x i).host.g l : ℝ) ∧
      Real.log ((Fm.D x i).host.g l) ≤ (Fm.CYL + 1) * (Fm.L x i).sc.L)) := by
  have hS := Fm.sizes x hx i
  have hQD := hS.2.2.2.2.2.2.1
  have hx0 : 0 < (Fm.L x i).sc.x := by linarith [(Fm.L x i).sc.one_lt_alt]
  have hq2 := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  refine ⟨size_parameter_bounds_of _ _ (Fm.params x hx i) (Fm.parT x hx i) CP AP ?_ ?_ ?_,
    size_tail_bounds_of _ _ (Fm.params x hx i) hS _ Cq ?_ ?_⟩
  · unfold placeRankTwoOne.PP
    refine mul_nonneg hCP (Real.rpow_nonneg ?_ _)
    have h1 : 0 ≤ (Fm.L x i).sc.L := by unfold Scale.L; exact (Real.rpow_pos_of_pos hx0 _).le
    have h2 := Real.log_nonneg (one_le_absDiscr (Fm.D x i))
    positivity
  · exact hPP x hx i
  · rw [Fm.Ct_eq x i, Fm.parT_Cb x hx i]; exact hCb
  · rw [Fm.params_CYL x hx i]
  · rw [Fm.Ct_eq x i]; exact hCq

end Formalism.MainNotions.DIV

end

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions

/- English proof (translation)
Establish `h` using `hEta.2.2.2.2.2.2.2.2`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hxe : 1 ≤ L.sc.x ^ L.sc.eps` using `Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hb0 : 0 < L.sc.b` using `by unfold Scale.b; exact Real.exp_pos _`.

Establish `hb' : 0 ≤ L.sc.b'` using `by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity`. Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k`.

Establish `: D.R.m ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hmr : (D.R.m : ℝ) ≤ D.R.r`. Establish `: D.R.m ≤ D.R.r` using `by unfold Ranks.r; have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions.

Establish `hd0` using `L.thickDensity_pos`. Establish `hd1` using `L.thickDensity_le_one`. Establish `hS0` using `L.Sc_pos`. Unfold `Formalism.MainNotions.szlA at h`. Establish `hmd : 0 < (D.R.m : ℝ) * L.de2` using `mul_pos (by linarith) hd0`.

Rewrite `h` using `[← mul_div_assoc, div_le_iff₀ hmd]`. Establish `l1 : (D.R.m : ℝ) * L.sc.b' ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc)` using `mul_le_mul hmr (by linarith) hb' (by linarith)`. Establish `l2 : (D.R.m : ℝ) * L.sc.b' * 2 ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x` using `mul_le_mul l1 hlx (by norm_num) (by positivity)`. Establish `l3 : (D.R.m : ℝ) * 1 ≤ (D.R.k : ℝ) * L.sc.x ^ L.sc.eps` using `mul_le_mul hmk hxe (by norm_num) (by linarith)`. Establish `l4 : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * ((D.R.k : ℝ) * L.sc.x ^ L.sc.eps)` using `mul_le_mul l2 l3 (by positivity) (by positivity)`.

Establish `u1 : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) ≤ (D.R.m : ℝ) * D.R.m * L.sc.b`. Establish `e : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) = (L.de2 * L.de2) * ((D.R.m : ℝ) * D.R.m * L.sc.b)`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Establish `: L.de2 * L.de2 ≤ 1` using `by nlinarith`.

Conclude with `mul_le_of_le_one_left (by positivity) this`. Establish `fin : (D.R.m : ℝ) * D.R.m * (2 * L.sc.b') ≤ (D.R.m : ℝ) * D.R.m * L.sc.b`. Establish `e : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) = (D.R.m : ℝ) * D.R.m * (2 * L.sc.b')` using `by ring`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_of_mul_le_mul_left fin (by positivity)`.
-/
theorem bprime_le_half (D : D7) (L : SizeData₂ D) (hEta : Formalism.MainNotions.SizeEta L) (hlx : 2 ≤ Real.log L.sc.x) :
    2 * L.sc.b' ≤ L.sc.b := by
  have h := hEta.2.2.2.2.2.2.2.2
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hxe : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have hb' : 0 ≤ L.sc.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hmr : (D.R.m : ℝ) ≤ D.R.r := by
    have : D.R.m ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hd0 := L.thickDensity_pos
  have hd1 := L.thickDensity_le_one
  have hS0 := L.Sc_pos
  unfold Formalism.MainNotions.szlA at h
  have hmd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos (by linarith) hd0
  rw [← mul_div_assoc, div_le_iff₀ hmd] at h

  have l1 : (D.R.m : ℝ) * L.sc.b' ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) :=
    mul_le_mul hmr (by linarith) hb' (by linarith)
  have l2 : (D.R.m : ℝ) * L.sc.b' * 2 ≤ (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x :=
    mul_le_mul l1 hlx (by norm_num) (by positivity)
  have l3 : (D.R.m : ℝ) * 1 ≤ (D.R.k : ℝ) * L.sc.x ^ L.sc.eps := mul_le_mul hmk hxe (by norm_num) (by linarith)
  have l4 : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) ≤
      (D.R.r : ℝ) * (L.sc.b' + L.Sc) * Real.log L.sc.x * ((D.R.k : ℝ) * L.sc.x ^ L.sc.eps) :=
    mul_le_mul l2 l3 (by positivity) (by positivity)

  have u1 : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) ≤ (D.R.m : ℝ) * D.R.m * L.sc.b := by
    have e : L.de2 * D.R.m * L.sc.b * ((D.R.m : ℝ) * L.de2) = (L.de2 * L.de2) * ((D.R.m : ℝ) * D.R.m * L.sc.b) := by
      ring
    rw [e]
    have : L.de2 * L.de2 ≤ 1 := by nlinarith
    exact mul_le_of_le_one_left (by positivity) this
  have fin : (D.R.m : ℝ) * D.R.m * (2 * L.sc.b') ≤ (D.R.m : ℝ) * D.R.m * L.sc.b := by
    have e : (D.R.m : ℝ) * L.sc.b' * 2 * ((D.R.m : ℝ) * 1) = (D.R.m : ℝ) * D.R.m * (2 * L.sc.b') := by ring
    linarith
  exact le_of_mul_le_mul_left fin (by positivity)

/- English proof (translation)
Take `⟨-, -, -, -, hll, -, -, -, -, -, -, -, -, hbT⟩` from `hSz`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hlx : 2 ≤ Real.log L.sc.x`. Establish `hpos : 0 < Real.log L.sc.x` using `Real.log_pos hx1`.

Use `(Real.le_log_iff_exp_le hpos).1 hll` as an intermediate fact. Establish `h3` using `Real.add_one_le_exp (1 : ℝ)`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hbb` using `bprime_le_half D L hEta hlx`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`.

Establish `hb2 : 2 ≤ L.sc.b`. Unfold `Scale.b`. Use `Real.add_one_le_exp L.sc.L` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hb' : 0 ≤ L.sc.b'` using `by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity`.

Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions. Establish `hw' : L.sc.w'' D.R.n ≤ L.sc.b'`. Unfold `Scale.w''`.

Conclude with `div_le_self hb' (by nlinarith)`. Establish `hbx : L.sc.b' / L.sc.x ≤ L.sc.b'` using `div_le_self hb' hx1.le`. Establish `hbx0 : 0 ≤ L.sc.b' / L.sc.x` using `by positivity`. Establish `hη0` using `L.etaSz_pos`. Establish `ht4 : (4 : ℝ) ≤ D.R.t`.

Establish `: 4 ≤ D.R.t` using `by have := D.R.rank_add_five_le; omega`. Conclude with `this` after adjusting the coercions. Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions.

Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Conclude with `this` after adjusting the coercions. Establish `hη : 4 * L.etaSz ≤ L.sc.b`. Establish `e1` using `hEta.2.1`.

Rewrite `e1` using `[le_div_iff₀ (by positivity)]`. Establish `e2 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3`. Establish `a1 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3` using `by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ D.R.t) (by linarith : (0:ℝ) ≤ D.R.t)]`. Establish `a2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3` using `one_le_pow₀ hk1`. Establish `a3 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f` using `by nlinarith`.

Use the polynomial consequences of the given equalities and inequalities. Use the polynomial consequences of the given equalities and inequalities. Establish `hwj : (placeRankTwoOne.wI D j τ : ℝ) = wj D j τ`. Rewrite using `[wI_cast_h]`. Unfold `DV.wSz wj`.

Rewrite using `[dif_pos ⟨h1, h2⟩, dif_pos (by omega)]`. Rewrite using `[hwj]`. Distinguish the cases in `htop : ((D.eTau τ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces`. Unfold `Host.topPlaces at htop`. Take `⟨a, ha, hae⟩` from `Finset.mem_image.1 htop`.

Establish `hw` using `L.win_top j h1 h2 τ ⟨a, ha⟩ hae.symm`. Establish `g1` using `L.bT_ge ⟨a, ha⟩`. Establish `g2` using `hbT ⟨a, ha⟩`. Apply the tactic sequence `constructor <;> linarith`. Distinguish the cases in `hthick : ((D.eTau τ : D.R.Psi) : D.R.GG) ∈ D.host.thickPlaces`.

Establish `hw` using `L.win_thick j h1 h2 τ hthick`. Apply the tactic sequence `constructor <;> linarith`. Establish `hw` using `L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, htop, hthick⟩`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem wI_win_of (D : D7) (L : SizeData₂ D) (Cs : ℝ) (hSz : placeRankTwoOne.Sizes D L Cs) (hEta : Formalism.MainNotions.SizeEta L)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    L.sc.w'' D.R.n ≤ (placeRankTwoOne.wI D j τ : ℝ) ∧ (placeRankTwoOne.wI D j τ : ℝ) ≤ 2 * L.sc.b := by
  obtain ⟨-, -, -, -, hll, -, -, -, -, -, -, -, -, hbT⟩ := hSz
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hx0 : 0 < L.sc.x := by linarith
  have hlx : 2 ≤ Real.log L.sc.x := by
    have hpos : 0 < Real.log L.sc.x := Real.log_pos hx1
    have := (Real.le_log_iff_exp_le hpos).1 hll
    have h3 := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hbb := bprime_le_half D L hEta hlx
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hb2 : 2 ≤ L.sc.b := by
    unfold Scale.b; have := Real.add_one_le_exp L.sc.L; linarith
  have hb' : 0 ≤ L.sc.b' := by unfold Scale.b' Scale.a Scale.X' Scale.b; positivity
  have hn1 : (1 : ℝ) ≤ D.R.n := by
    have : 1 ≤ D.R.n := D.R.ord_pos
    exact_mod_cast this
  have hw' : L.sc.w'' D.R.n ≤ L.sc.b' := by
    unfold Scale.w''
    exact div_le_self hb' (by nlinarith)
  have hbx : L.sc.b' / L.sc.x ≤ L.sc.b' := div_le_self hb' hx1.le
  have hbx0 : 0 ≤ L.sc.b' / L.sc.x := by positivity
  have hη0 := L.etaSz_pos
  have ht4 : (4 : ℝ) ≤ D.R.t := by
    have : 4 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
    exact_mod_cast this
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hη : 4 * L.etaSz ≤ L.sc.b := by
    have e1 := hEta.2.1
    rw [le_div_iff₀ (by positivity)] at e1
    have e2 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f * (D.R.k : ℝ) ^ 3 := by
      have a1 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 := by nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ D.R.t) (by linarith : (0:ℝ) ≤ D.R.t)]
      have a2 : (1 : ℝ) ≤ (D.R.k : ℝ) ^ 3 := one_le_pow₀ hk1
      have a3 : (4 : ℝ) ≤ (D.R.t : ℝ) ^ 3 * D.R.f := by nlinarith
      nlinarith
    nlinarith
  have hwj : (placeRankTwoOne.wI D j τ : ℝ) = wj D j τ := by
    rw [wI_cast_h]
    unfold DV.wSz wj
    rw [dif_pos ⟨h1, h2⟩, dif_pos (by omega)]
  rw [hwj]
  by_cases htop : ((D.eTau τ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces
  · unfold Host.topPlaces at htop
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.1 htop
    have hw := L.win_top j h1 h2 τ ⟨a, ha⟩ hae.symm
    have g1 := L.bT_ge ⟨a, ha⟩
    have g2 := hbT ⟨a, ha⟩
    constructor <;> linarith
  · by_cases hthick : ((D.eTau τ : D.R.Psi) : D.R.GG) ∈ D.host.thickPlaces
    · have hw := L.win_thick j h1 h2 τ hthick
      constructor <;> linarith
    · have hw := L.win_thin j h1 h2 τ ⟨(D.eTau τ).2, htop, hthick⟩
      constructor <;> linarith

/- English proof (translation)
Take `⟨-, -, -, -, -, hCond, hQD, -, -, -, -, -, -, hEta, -, -, hDel, hW, -⟩` from `hS`. Establish `hx0 : 0 < L.sc.x` using `by linarith`. Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Use `set p : ℝ := placeRankTwoOne.PP D L CP AP with hp`. Use `set y : ℝ := L.sc.x ^ (L.sc.eps / 4) with hyd`.

Establish `hLy : L.sc.L = y ^ 4`. Unfold `Scale.L`. Rewrite using `[hyd, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hy3 : (27 : ℝ) ≤ y ^ 3`. Use `pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hy 3` as an intermediate fact. Evaluate the numerical expressions using `at this`. Conclude with `this`.

Establish `hL27 : 27 * y ≤ L.sc.L`. Rewrite using `[hLy, show y ^ 4 = y ^ 3 * y by ring]`. Conclude with `mul_le_mul_of_nonneg_right hy3 (by linarith)`. Establish `hL81 : 81 ≤ L.sc.L` using `by linarith`. Establish `hw0 : 0 ≤ L.sc.w'' D.R.n`.

Unfold `Scale.w'' Scale.b' Scale.a Scale.X' Scale.b`. Check the signs of the components of the expression. Establish `hb0 : 0 < L.sc.b` using `by unfold Scale.b; exact Real.exp_pos _`. Establish `hlb : Real.log L.sc.b = L.sc.L` using `by unfold Scale.b; exact Real.log_exp _`. Establish `hη0` using `L.etaSz_pos`.

Establish `hS0` using `L.Sc_pos`. Establish `hk0 : (0 : ℝ) < D.R.k`. Establish `: 0 < D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hkt : (D.R.k : ℝ) ≤ D.R.t`.

Establish `: D.R.k ≤ D.R.t` using `by have := D.R.rank_add_five_le; have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `ht0 : (0 : ℝ) < D.R.t` using `by linarith`. Establish `hA : p * L.etaSz ≤ L.sc.w'' D.R.n / 2`. Establish `h1 : p * L.etaSz ≤ 2 * D.R.t * L.etaSz` using `mul_le_mul_of_nonneg_right hp2t hη0.le`.

Establish `h2` using `hEta.2.2.2.1`. Establish `h3 : L.sc.w'' D.R.n / L.sc.x * L.sc.x = L.sc.w'' D.R.n` using `by field_simp`. Establish `h4 : 0 ≤ L.sc.w'' D.R.n / L.sc.x` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Establish `hDel0 : (0 : ℝ) < (D.s.Del : ℝ)`.

Use `L.Sc_eq` as an intermediate fact. Assume the negation of the conclusion as `hneg`. Use `push Not at hneg`. Establish `: L.Sc ≤ 0` using `by rw [L.Sc_eq]; nlinarith`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hq2` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)`. Establish `hd2` using `two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)`. Establish `hc1 : 1 ≤ Formalism.MainNotions.szCond L`. Unfold `Formalism.MainNotions.szCond`. Establish `hq' : (2 : ℝ) ≤ D.host.q` using `by exact_mod_cast hq2`.

Establish `hd' : (2 : ℝ) ≤ D.host.d` using `by exact_mod_cast hd2`. Establish `hn1 : (1 : ℝ) ≤ D.R.n`. Establish `: 1 ≤ D.R.n` using `D.R.ord_pos`. Conclude with `this` after adjusting the coercions. Establish `: (1 : ℝ) ≤ (D.host.QS : ℝ)` using `by exact_mod_cast D.host.QS_pos`.

Establish `: (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hlt : Real.log D.R.t ≤ L.sc.L / 300`. Establish `h1 : (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b` using `le_trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)) hCond`. Establish `h2` using `Real.log_le_log (by positivity) h1`.

Rewrite `h2` using `[Real.log_pow, Real.log_sqrt hb0.le, hlb]`. Move the coercions through the operations in `at h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlk : Real.log D.R.k ≤ L.sc.L / 300` using `(Real.log_le_log hk0 hkt).trans hlt`. Establish `hlD : Real.log (D.s.Del : ℝ) ≤ y / 2` using `hDel.2.2.1`.

Establish `h16 : Real.log 16 = 4 * Real.log 2`. Rewrite using `[show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num`. Establish `hB : 16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n`. Use `le_trans ?_ hW` and prove the remaining obligations. Establish `hpos : 0 < 16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ)` using `by positivity`.

Rewrite using `[← Real.log_le_log_iff hpos (Real.sqrt_pos.2 hb0), Real.log_sqrt hb0.le, hlb, Real.log_mul (by positivity) hDel0.ne', Real.log_mul (by positivity) hk0.ne', Real.log_mul (by norm_num) ht0.ne', h16]`. Use `Real.log_two_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hBS : p * L.Sc ≤ L.sc.w'' D.R.n / 2`. Establish `h1 : p * L.Sc ≤ 2 * D.R.t * L.Sc` using `mul_le_mul_of_nonneg_right hp2t hS0.le`.

Establish `h2 : 2 * (D.R.t : ℝ) * L.Sc = (16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ)) / 2`. Rewrite using `[L.Sc_eq]`. Expand and normalize the polynomial expressions, which then agree. Combine the linear equalities and inequalities to obtain the conclusion. Establish `: p * (L.Sc + L.etaSz) = p * L.Sc + p * L.etaSz` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem size_product_bound_of (D : D7) (L : SizeData₂ D) (CP AP : ℝ)
    (hp2t : placeRankTwoOne.PP D L CP AP ≤ 2 * D.R.t) (hS : Formalism.MainNotions.SizesAt L)
    (hx4 : 4 ≤ L.sc.x) (hy : 3 ≤ L.sc.x ^ (L.sc.eps / 4)) :
    placeRankTwoOne.PP D L CP AP * (L.Sc + L.etaSz) ≤ L.sc.w'' D.R.n := by
  obtain ⟨-, -, -, -, -, hCond, hQD, -, -, -, -, -, -, hEta, -, -, hDel, hW, -⟩ := hS
  have hx0 : 0 < L.sc.x := by linarith
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  set p : ℝ := placeRankTwoOne.PP D L CP AP with hp
  set y : ℝ := L.sc.x ^ (L.sc.eps / 4) with hyd
  have hLy : L.sc.L = y ^ 4 := by
    unfold Scale.L
    rw [hyd, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    congr 1; push_cast; ring
  have hy3 : (27 : ℝ) ≤ y ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hy 3
    norm_num at this; exact this
  have hL27 : 27 * y ≤ L.sc.L := by
    rw [hLy, show y ^ 4 = y ^ 3 * y by ring]
    exact mul_le_mul_of_nonneg_right hy3 (by linarith)
  have hL81 : 81 ≤ L.sc.L := by linarith
  have hw0 : 0 ≤ L.sc.w'' D.R.n := by
    unfold Scale.w'' Scale.b' Scale.a Scale.X' Scale.b; positivity
  have hb0 : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have hlb : Real.log L.sc.b = L.sc.L := by unfold Scale.b; exact Real.log_exp _
  have hη0 := L.etaSz_pos
  have hS0 := L.Sc_pos
  have hk0 : (0 : ℝ) < D.R.k := by
    have : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hkt : (D.R.k : ℝ) ≤ D.R.t := by
    have : D.R.k ≤ D.R.t := by have := D.R.rank_add_five_le; have := D.R.two_le_m; omega
    exact_mod_cast this
  have ht0 : (0 : ℝ) < D.R.t := by linarith

  have hA : p * L.etaSz ≤ L.sc.w'' D.R.n / 2 := by
    have h1 : p * L.etaSz ≤ 2 * D.R.t * L.etaSz := mul_le_mul_of_nonneg_right hp2t hη0.le
    have h2 := hEta.2.2.2.1
    have h3 : L.sc.w'' D.R.n / L.sc.x * L.sc.x = L.sc.w'' D.R.n := by field_simp
    have h4 : 0 ≤ L.sc.w'' D.R.n / L.sc.x := by positivity
    nlinarith

  have hDel0 : (0 : ℝ) < (D.s.Del : ℝ) := by
    have := L.Sc_eq
    by_contra hneg
    push Not at hneg
    have : L.Sc ≤ 0 := by rw [L.Sc_eq]; nlinarith
    linarith
  have hq2 := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.1)
  have hd2 := two_le_of_log_pos _ (lt_of_lt_of_le (Real.rpow_pos_of_pos hx0 _) hQD.2.2.2.1)
  have hc1 : 1 ≤ Formalism.MainNotions.szCond L := by
    unfold Formalism.MainNotions.szCond
    have hq' : (2 : ℝ) ≤ D.host.q := by exact_mod_cast hq2
    have hd' : (2 : ℝ) ≤ D.host.d := by exact_mod_cast hd2
    have hn1 : (1 : ℝ) ≤ D.R.n := by
      have : 1 ≤ D.R.n := D.R.ord_pos
      exact_mod_cast this
    have : (1 : ℝ) ≤ (D.host.QS : ℝ) := by exact_mod_cast D.host.QS_pos
    have : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q := by nlinarith
    nlinarith
  have hlt : Real.log D.R.t ≤ L.sc.L / 300 := by
    have h1 : (D.R.t : ℝ) ^ 150 ≤ Real.sqrt L.sc.b :=
      le_trans (le_mul_of_one_le_left (by positivity) (one_le_pow₀ hc1)) hCond
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow, Real.log_sqrt hb0.le, hlb] at h2
    push_cast at h2
    linarith
  have hlk : Real.log D.R.k ≤ L.sc.L / 300 := (Real.log_le_log hk0 hkt).trans hlt
  have hlD : Real.log (D.s.Del : ℝ) ≤ y / 2 := hDel.2.2.1
  have h16 : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hB : 16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ) ≤ L.sc.w'' D.R.n := by
    refine le_trans ?_ hW
    have hpos : 0 < 16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ) := by positivity
    rw [← Real.log_le_log_iff hpos (Real.sqrt_pos.2 hb0), Real.log_sqrt hb0.le, hlb,
      Real.log_mul (by positivity) hDel0.ne', Real.log_mul (by positivity) hk0.ne',
      Real.log_mul (by norm_num) ht0.ne', h16]
    have := Real.log_two_lt_d9
    linarith
  have hBS : p * L.Sc ≤ L.sc.w'' D.R.n / 2 := by
    have h1 : p * L.Sc ≤ 2 * D.R.t * L.Sc := mul_le_mul_of_nonneg_right hp2t hS0.le
    have h2 : 2 * (D.R.t : ℝ) * L.Sc = (16 * (D.R.t : ℝ) * D.R.k * (D.s.Del : ℝ)) / 2 := by
      rw [L.Sc_eq]; ring
    linarith
  have : p * (L.Sc + L.etaSz) = p * L.Sc + p * L.etaSz := by ring
  linarith

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k`.

Establish `: D.R.m ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions. Establish `hf0 : 0 < D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Establish `hf1 : (1 : ℝ) ≤ D.R.f` using `by exact_mod_cast hf0`. Establish `hr2 : 2 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`.

Establish `hD1 : (1 : ℝ) ≤ (T.Dp : ℝ)`. Establish `: 1 ≤ T.Dp`. Rewrite using `[T.Dp_eq]`. Conclude with `Nat.mul_pos hf0 (Nat.choose_pos hr2)`. Conclude with `this` after adjusting the coercions.

Establish `hxCp : 1 ≤ L.sc.x ^ T.Cp` using `Real.one_le_rpow hx1.le T.Cp_nonneg`. Establish `hmd : 0 < (D.R.m : ℝ) * L.de2` using `mul_pos (by linarith) L.thickDensity_pos`. Establish `hPT : T.PP ≤ (T.TO : ℝ)`. Use `le_trans ?_ T.TO_ge` and prove the remaining obligations. Rewrite using `[le_div_iff₀ hmd]`.

Establish `b0 : (D.R.m : ℝ) * L.de2 ≤ D.R.k`. Use `L.thickDensity_le_one` as an intermediate fact. Use `L.thickDensity_pos` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `b1 : T.PP * ((D.R.m : ℝ) * L.de2) ≤ T.PP * D.R.k` using `mul_le_mul_of_nonneg_left b0 (by linarith)`.

Establish `b2 : T.PP ≤ T.PP ^ 4` using `le_self_pow₀ h1 (by norm_num)`. Establish `b3 : T.PP ^ 4 ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3` using `le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD1)`. Establish `b4 : T.PP * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k` using `mul_le_mul_of_nonneg_right (b2.trans b3) (by linarith)`. Establish `b5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f` using `le_mul_of_one_le_right (by positivity) hf1`. Establish `b6 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp` using `le_mul_of_one_le_right (by positivity) hxCp`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hTt : (T.TO : ℝ) ≤ D.R.t`. Establish `: T.TO ≤ D.R.t`. Establish `s` using `T.split`. Establish `n1` using `T.nP_ge`.

Establish `n2 : T.TO ≤ T.TO * T.nWn` using `Nat.le_mul_of_pos_right _ hnW`. Establish `n3 : D.R.r ≤ 8 * D.R.f * D.R.r` using `Nat.le_mul_of_pos_left _ (by omega)`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem PP_le_t_of_split (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) (CP AP : ℝ)
    (hPP : placeRankTwoOne.PP D L CP AP ≤ T.PP) (h1 : 1 ≤ T.PP) (hnW : 1 ≤ T.nWn) :
    placeRankTwoOne.PP D L CP AP ≤ D.R.t := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have : D.R.m ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hf0 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
  have hf1 : (1 : ℝ) ≤ D.R.f := by exact_mod_cast hf0
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hD1 : (1 : ℝ) ≤ (T.Dp : ℝ) := by
    have : 1 ≤ T.Dp := by
      rw [T.Dp_eq]
      exact Nat.mul_pos hf0 (Nat.choose_pos hr2)
    exact_mod_cast this
  have hxCp : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow hx1.le T.Cp_nonneg
  have hmd : 0 < (D.R.m : ℝ) * L.de2 := mul_pos (by linarith) L.thickDensity_pos
  have hPT : T.PP ≤ (T.TO : ℝ) := by
    refine le_trans ?_ T.TO_ge
    rw [le_div_iff₀ hmd]
    have b0 : (D.R.m : ℝ) * L.de2 ≤ D.R.k := by
      have := L.thickDensity_le_one; have := L.thickDensity_pos; nlinarith
    have b1 : T.PP * ((D.R.m : ℝ) * L.de2) ≤ T.PP * D.R.k := mul_le_mul_of_nonneg_left b0 (by linarith)
    have b2 : T.PP ≤ T.PP ^ 4 := le_self_pow₀ h1 (by norm_num)
    have b3 : T.PP ^ 4 ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 := le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD1)
    have b4 : T.PP * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k :=
      mul_le_mul_of_nonneg_right (b2.trans b3) (by linarith)
    have b5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f :=
      le_mul_of_one_le_right (by positivity) hf1
    have b6 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤
        T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp :=
      le_mul_of_one_le_right (by positivity) hxCp
    linarith
  have hTt : (T.TO : ℝ) ≤ D.R.t := by
    have : T.TO ≤ D.R.t := by
      have s := T.split
      have n1 := T.nP_ge
      have n2 : T.TO ≤ T.TO * T.nWn := Nat.le_mul_of_pos_right _ hnW
      have n3 : D.R.r ≤ 8 * D.R.f * D.R.r := Nat.le_mul_of_pos_left _ (by omega)
      omega
    exact_mod_cast this
  linarith

def sgR (D : D7) (τ : D.what₂.Tau) (i : ℕ) : ℝ := ((DV.sigPar D τ i : ℚ) : ℝ)

/- English proof (translation)
Unfold `DV.sigPar`. Rewrite using `[dif_neg (by omega)]`. Simplify using `only [Nat.add_sub_cancel_left]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sigPar_low (D : D7) (τ : D.what₂.Tau) (a : ℕ) :
    DV.sigPar D τ (D.R.k - 1 + a) = -(if h : a < D.R.m then (D.hc τ).b ⟨a, h⟩ else 0) := by
  unfold DV.sigPar
  rw [dif_neg (by omega)]
  simp only [Nat.add_sub_cancel_left]
  split_ifs <;> simp

/- English proof (translation)
Unfold `sgR DV.sigPar`. Rewrite using `[dif_pos h]`.
-/
theorem sgR_cloud (D : D7) (τ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k - 1) :
    sgR D τ i = (((D.hc τ).v ⟨i, h⟩ : ℚ) : ℝ) := by
  unfold sgR DV.sigPar
  rw [dif_pos h]

/- English proof (translation)
Unfold `sgR`. Rewrite using `[sigPar_low, dif_pos h]`. Use `push_cast`. Both sides reduce to the same expression.
-/
theorem sgR_low (D : D7) (τ : D.what₂.Tau) (a : ℕ) (h : a < D.R.m) :
    sgR D τ (D.R.k - 1 + a) = -(((D.hc τ).b ⟨a, h⟩ : ℚ) : ℝ) := by
  unfold sgR
  rw [sigPar_low, dif_pos h]
  push_cast
  rfl

/- English proof (translation)
Introduce `l hl`. Proceed by induction on `l, hl using Nat.le_induction with`. Consider the case `base => intro _`. Simplify using the standard rewrite rules. Consider the case `succ l hl ih`.

Introduce `h`. Establish `h1` using `ih (by omega)`. Establish `h2` using `hs l (by omega) h`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem steps_sum (s : ℕ → ℝ) (lo r : ℕ) (G : ℝ) (hs : ∀ i, lo ≤ i → i + 1 < r → G ≤ s i - s (i + 1)) (i : ℕ) (hi : lo ≤ i) :
    ∀ l, i ≤ l → l < r → ((l : ℝ) - i) * G ≤ s i - s l := by
  intro l hl
  induction l, hl using Nat.le_induction with
  | base => intro _; simp
  | succ l hl ih =>
    intro h
    have h1 := ih (by omega)
    have h2 := hs l (by omega) h
    push_cast
    linarith

/- English proof (translation)
Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `hm` using `D.R.two_le_m`. Break down `Nat.lt_trichotomy (i + 1) (D.R.k - 1) with h | h | h` into its components or cases. Rewrite using `[sgR_cloud D τ i (by omega), sgR_cloud D τ (i + 1) h]`.

Establish `e` using `D.s.cloud_gap D.u₀ τ i h`. Rewrite `e` using `[D.hcW_base]`. Establish `e'` using `congrArg (fun q : ℚ => (q : ℝ)) e`. Simplify using `only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] at e'`. Rewrite using `[e']`.

Conclude with `h1`. Establish `e0 : i + 1 = D.R.k - 1 + 0` using `by omega`. Rewrite using `[sgR_cloud D τ i (by omega), e0, sgR_low D τ 0 (by omega)]`. Use `(L.cloud_v τ ⟨i, by omega⟩).1` as an intermediate fact. Use `h3 (by omega)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a` from `⟨i - (D.R.k - 1), by omega⟩`. Substitute `ha` using the available equality. Rewrite using `[sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]`. Use `(P.nodes_gap τ a (by omega)).1` as an intermediate fact.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sgR_step (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (τ : D.what₂.Tau) (G : ℝ)
    (h1 : G ≤ 4 * ((D.s.Del : ℚ) : ℝ)) (h2 : G ≤ LevelStarExponents.h0 L)
    (h3 : ∀ hm : 0 < D.R.m, G ≤ (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ)) (i : ℕ) (hi : i + 1 < D.R.r) :
    G ≤ sgR D τ i - sgR D τ (i + 1) := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have hm := D.R.two_le_m
  rcases Nat.lt_trichotomy (i + 1) (D.R.k - 1) with h | h | h
  · rw [sgR_cloud D τ i (by omega), sgR_cloud D τ (i + 1) h]
    have e := D.s.cloud_gap D.u₀ τ i h
    rw [D.hcW_base] at e
    have e' := congrArg (fun q : ℚ => (q : ℝ)) e
    simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_ofNat] at e'
    rw [e']
    exact h1
  · have e0 : i + 1 = D.R.k - 1 + 0 := by omega
    rw [sgR_cloud D τ i (by omega), e0, sgR_low D τ 0 (by omega)]
    have := (L.cloud_v τ ⟨i, by omega⟩).1
    have := h3 (by omega)
    linarith
  · obtain ⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a := ⟨i - (D.R.k - 1), by omega⟩
    subst ha
    rw [sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]
    have := (P.nodes_gap τ a (by omega)).1
    push_cast at this
    linarith

/- English proof (translation)
Take `⟨a, ha⟩` from `R.k_even`. Take `⟨b, hb⟩` from `R.m_even`. Take `⟨c, hc⟩` from `R.t_odd`. Establish `hm` using `R.two_le_m`. Establish `h1 : R.nV / 2 = a + b + c` using `by unfold Ranks.nV Ranks.r; omega`.

Rewrite using `[h1, ha, hb, hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nV_half_cast (R : Ranks) : ((R.nV / 2 : ℕ) : ℝ) = ((R.k : ℝ) + R.m - 1 + R.t) / 2 := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hm := R.two_le_m
  have h1 : R.nV / 2 = a + b + c := by unfold Ranks.nV Ranks.r; omega
  rw [h1, ha, hb, hc]
  push_cast
  ring

/- English proof (translation)
Establish `e : ((D.what₂.kaBig j τ ⟨i.1, h⟩ : ℤ) : ℚ) = DV.aPlusQ D j τ i.1` using `(hK j h1 h2 τ).1 ⟨i.1, h⟩`. Rewrite `e` using `[DV.aPlusQ_eq]`. Establish `e'` using `congrArg (fun q : ℚ => (q : ℝ)) e`. Simplify using `only [Rat.cast_intCast] at e'`. Unfold `DV.kapW`.

Rewrite using `[dif_pos h, Int.cast_add, Int.cast_natCast, e', nV_half_cast, ← DV.eQ_cast]`. Unfold `sgR`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kapW_big (D : D7) (hK : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (i : Fin D.R.r)
    (h : i.1 < (D.R.sigW j).1) :
    (DV.kapW D j τ i : ℝ) =
      sgR D τ i.1 + DV.wSz D j τ - ((D.R.k : ℝ) + j - 2 - i.1) - ((D.R.t : ℝ) + 1) / 2 +
        ((D.R.k : ℝ) + D.R.m - 1 + D.R.t) / 2 := by
  have e : ((D.what₂.kaBig j τ ⟨i.1, h⟩ : ℤ) : ℚ) = DV.aPlusQ D j τ i.1 := (hK j h1 h2 τ).1 ⟨i.1, h⟩
  rw [DV.aPlusQ_eq] at e
  have e' := congrArg (fun q : ℚ => (q : ℝ)) e
  simp only [Rat.cast_intCast] at e'
  unfold DV.kapW
  rw [dif_pos h, Int.cast_add, Int.cast_natCast, e', nV_half_cast, ← DV.eQ_cast]
  unfold sgR
  push_cast
  ring

/- English proof (translation)
Establish `hp : (D.R.sigW j).1 = D.R.k + j - 1` using `rfl`. Establish `hq : (D.R.sigW j).2 = D.R.m - j` using `rfl`. Establish `hi` using `i.2`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hk` using `D.R.m_add_three_le_k`.

Establish `hc : i.1 - (D.R.sigW j).1 < (D.R.sigW j).2` using `by omega`. Establish `e : ((D.what₂.kaSmall j τ ⟨i.1 - (D.R.sigW j).1, hc⟩ : ℤ) : ℚ) = -DV.aMinusQ D j τ (i.1 - (D.R.sigW j).1)` using `(hK j h1 h2 τ).2 ⟨_, hc⟩`. Establish `hs : DV.sigPar D τ i.1 = -(if h : j + (i.1 - (D.R.sigW j).1) < D.R.m then (D.hc τ).b ⟨j + (i.1 - (D.R.sigW j).1), h⟩ else 0)`. Establish `e1 : i.1 = D.R.k - 1 + (j + (i.1 - (D.R.sigW j).1))` using `by omega`. Combine the equalities or inequalities in the displayed calculation.

Establish `e2 : ((D.what₂.kaSmall j τ ⟨i.1 - (D.R.sigW j).1, hc⟩ : ℤ) : ℚ) = DV.sigPar D τ i.1 + DV.eQ D j τ + ((D.R.t : ℚ) + 1 + 2 * ((i.1 - (D.R.sigW j).1 : ℕ) : ℚ)) / 2`. Rewrite using `[e, hs]`. Unfold `DV.aMinusQ`. Expand and normalize the polynomial expressions, which then agree. Establish `e'` using `congrArg (fun q : ℚ => (q : ℝ)) e2`.

Simplify using `only [Rat.cast_intCast] at e'`. Establish `hcast : ((i.1 - (D.R.sigW j).1 : ℕ) : ℝ) = (i.1 : ℝ) - ((D.R.k : ℝ) + j - 1)`. Rewrite using `[Nat.cast_sub h, hp, Nat.cast_sub (by omega)]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Unfold `DV.kapW`. Rewrite using `[dif_neg (by omega), dif_pos hc, Int.cast_sub, Int.cast_natCast, e', nV_half_cast, ← DV.eQ_cast]`. Unfold `sgR`. Use `push_cast`. Rewrite using `[hcast]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem kapW_small (D : D7) (hK : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (i : Fin D.R.r)
    (h : (D.R.sigW j).1 ≤ i.1) :
    (DV.kapW D j τ i : ℝ) =
      sgR D τ i.1 + DV.wSz D j τ + ((D.R.t : ℝ) + 1) / 2 + ((i.1 : ℝ) - ((D.R.k : ℝ) + j - 1)) -
        ((D.R.k : ℝ) + D.R.m - 1 + D.R.t) / 2 := by
  have hp : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have hq : (D.R.sigW j).2 = D.R.m - j := rfl
  have hi := i.2
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have hc : i.1 - (D.R.sigW j).1 < (D.R.sigW j).2 := by omega
  have e : ((D.what₂.kaSmall j τ ⟨i.1 - (D.R.sigW j).1, hc⟩ : ℤ) : ℚ) = -DV.aMinusQ D j τ (i.1 - (D.R.sigW j).1) :=
    (hK j h1 h2 τ).2 ⟨_, hc⟩
  have hs : DV.sigPar D τ i.1 =
      -(if h : j + (i.1 - (D.R.sigW j).1) < D.R.m then (D.hc τ).b ⟨j + (i.1 - (D.R.sigW j).1), h⟩ else 0) := by
    have e1 : i.1 = D.R.k - 1 + (j + (i.1 - (D.R.sigW j).1)) := by omega
    calc DV.sigPar D τ i.1 = DV.sigPar D τ (D.R.k - 1 + (j + (i.1 - (D.R.sigW j).1))) := congrArg _ e1
      _ = _ := sigPar_low D τ _
  have e2 : ((D.what₂.kaSmall j τ ⟨i.1 - (D.R.sigW j).1, hc⟩ : ℤ) : ℚ) =
      DV.sigPar D τ i.1 + DV.eQ D j τ + ((D.R.t : ℚ) + 1 + 2 * ((i.1 - (D.R.sigW j).1 : ℕ) : ℚ)) / 2 := by
    rw [e, hs]
    unfold DV.aMinusQ
    ring
  have e' := congrArg (fun q : ℚ => (q : ℝ)) e2
  simp only [Rat.cast_intCast] at e'
  have hcast : ((i.1 - (D.R.sigW j).1 : ℕ) : ℝ) = (i.1 : ℝ) - ((D.R.k : ℝ) + j - 1) := by
    rw [Nat.cast_sub h, hp, Nat.cast_sub (by omega)]
    push_cast
    ring
  unfold DV.kapW
  rw [dif_neg (by omega), dif_pos hc, Int.cast_sub, Int.cast_natCast, e', nV_half_cast, ← DV.eQ_cast]
  unfold sgR
  push_cast
  rw [hcast]
  ring

/- English proof (translation)
Distinguish the cases in `hi : i.1 < (D.R.sigW j).1`. Rewrite using `[kapW_big D hK j h1 h2 τ i hi, kapW_big D hK j h1 h2 τ i' (h.1 hi)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hi' : ¬ i'.1 < (D.R.sigW j).1` using `fun h' => hi (h.2 h')`. Rewrite using `[kapW_small D hK j h1 h2 τ i (by omega), kapW_small D hK j h1 h2 τ i' (by omega)]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem kapW_sub_same (D : D7) (hK : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (i i' : Fin D.R.r)
    (h : i.1 < (D.R.sigW j).1 ↔ i'.1 < (D.R.sigW j).1) :
    (DV.kapW D j τ i : ℝ) - DV.kapW D j τ i' = sgR D τ i.1 - sgR D τ i'.1 + ((i.1 : ℝ) - i'.1) := by
  by_cases hi : i.1 < (D.R.sigW j).1
  · rw [kapW_big D hK j h1 h2 τ i hi, kapW_big D hK j h1 h2 τ i' (h.1 hi)]
    ring
  · have hi' : ¬ i'.1 < (D.R.sigW j).1 := fun h' => hi (h.2 h')
    rw [kapW_small D hK j h1 h2 τ i (by omega), kapW_small D hK j h1 h2 τ i' (by omega)]
    ring

/- English proof (translation)
Rewrite using `[kapW_big D hK j h1 h2 τ i hi, kapW_small D hK j h1 h2 τ l hl]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem kapW_sub_bar (D : D7) (hK : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (i l : Fin D.R.r)
    (hi : i.1 < (D.R.sigW j).1) (hl : (D.R.sigW j).1 ≤ l.1) :
    (DV.kapW D j τ i : ℝ) - DV.kapW D j τ l =
      sgR D τ i.1 - sgR D τ l.1 + ((i.1 : ℝ) - l.1) + ((D.R.k : ℝ) + D.R.m - 1) := by
  rw [kapW_big D hK j h1 h2 τ i hi, kapW_small D hK j h1 h2 τ l hl]
  ring

/- English proof (translation)
Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hk` using `D.R.m_add_three_le_k`. Take `⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a` from `⟨i - (D.R.k - 1), by omega⟩`. Substitute `ha` using the available equality. Rewrite using `[sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]`.

Use `(P.nodes_gap τ a (by omega)).1` as an intermediate fact. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sgR_step_low (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (τ : D.what₂.Tau) (i : ℕ) (hlo : D.R.k - 1 ≤ i)
    (hi : i + 1 < D.R.r) : LevelStarExponents.h0 L ≤ sgR D τ i - sgR D τ (i + 1) := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a := ⟨i - (D.R.k - 1), by omega⟩
  subst ha
  rw [sgR_low D τ a (by omega), Nat.add_assoc, sgR_low D τ (a + 1) (by omega)]
  have := (P.nodes_gap τ a (by omega)).1
  push_cast at this
  linarith

/- English proof (translation)
Establish `h : 1 ≤ R.k + R.m` using `by have := R.two_le_m; omega`. Unfold `Ranks.r`. Move the coercions through the operations in `[Nat.cast_sub h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem r_cast (R : Ranks) : (R.r : ℝ) = (R.k : ℝ) + R.m - 1 := by
  have h : 1 ≤ R.k + R.m := by have := R.two_le_m; omega
  unfold Ranks.r
  push_cast [Nat.cast_sub h]
  ring

/- English proof (translation)
Unfold `DV.wSz`. Rewrite using `[dif_pos ⟨h1, h2⟩]`.
-/
theorem wSz_eq (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) :
    DV.wSz D j τ = (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
  unfold DV.wSz
  rw [dif_pos ⟨h1, h2⟩]

/- English proof (translation)
Establish `h` using `P.h0_ge.2.2.2.2.1`. Establish `h1 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3` using `by positivity`. Establish `h2 : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem six_le_h0 (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) : 6 ≤ LevelStarExponents.h0 L := by
  have h := P.h0_ge.2.2.2.2.1
  have h1 : (0 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
  have h2 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  linarith

/- English proof (translation)
Establish `hb` using `abs_le.1 (L.be_close τ ⟨0, hm⟩ ⟨j - 1, by omega⟩)`. Rewrite `hw` using `[wSz_eq D j h1 h2 τ]`. Move the coercions through the operations in `at hb`. Establish `he` using `L.etaSz_pos`. Establish `hm2 : (2 : ℝ) ≤ D.R.m` using `by exact_mod_cast D.R.two_le_m`.

Establish `ht : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Establish `h3 : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz`. Use `mul_le_mul_of_nonneg_right ?_ he.le` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities. Establish `h4` using `P.mteta`.

Establish `h5 : LevelStarExponents.h0 L ≤ L.etaSz`. Unfold `LevelStarExponents.h0`. Conclude with `div_le_self he.le (by linarith)`. Combine the linear relations using `[hb.1]`.
-/
theorem minimalGap_le_first_lowerRowParameter (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau)
    (hw : L.sc.w'' D.R.n ≤ DV.wSz D j τ) (hm : 0 < D.R.m) : LevelStarExponents.h0 L ≤ (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) := by
  have hb := abs_le.1 (L.be_close τ ⟨0, hm⟩ ⟨j - 1, by omega⟩)
  rw [wSz_eq D j h1 h2 τ] at hw
  push_cast at hb
  have he := L.etaSz_pos
  have hm2 : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have h3 : 2 * L.etaSz ≤ (D.R.m : ℝ) * ((D.R.t : ℝ) + 1) * L.etaSz := by
    refine mul_le_mul_of_nonneg_right ?_ he.le
    nlinarith
  have h4 := P.mteta
  have h5 : LevelStarExponents.h0 L ≤ L.etaSz := by
    unfold LevelStarExponents.h0
    exact div_le_self he.le (by linarith)
  linarith [hb.1]

/- English proof (translation)
Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hk` using `D.R.m_add_three_le_k`. Take `⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a` from `⟨i - (D.R.k - 1), by omega⟩`. Substitute `ha` using the available equality. Rewrite using `[sgR_low D τ a (by omega), wSz_eq D j h1 h2 τ]`.

Establish `hb` using `L.be_close τ ⟨a, by omega⟩ ⟨j - 1, by omega⟩`. Move the coercions through the operations in `at hb`. Rewrite using `[← abs_neg]`. Use `hb using 2` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sgR_be (D : D7) (L : SizeData₂ D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (τ : D.what₂.Tau) (i : ℕ)
    (hlo : D.R.k - 1 ≤ i) (hi : i < D.R.r) : |sgR D τ i + DV.wSz D j τ| ≤ L.etaSz := by
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  obtain ⟨a, ha⟩ : ∃ a, i = D.R.k - 1 + a := ⟨i - (D.R.k - 1), by omega⟩
  subst ha
  rw [sgR_low D τ a (by omega), wSz_eq D j h1 h2 τ]
  have hb := L.be_close τ ⟨a, by omega⟩ ⟨j - 1, by omega⟩
  push_cast at hb
  rw [← abs_neg]
  convert hb using 2
  ring

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hk1 : (1 : ℝ) ≤ D.R.k`. Establish `: 1 ≤ D.R.k` using `by have := D.R.m_add_three_le_k; omega`. Conclude with `this` after adjusting the coercions.

Establish `hm1 : (1 : ℝ) ≤ D.R.m`. Establish `: 1 ≤ D.R.m` using `by have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`.

Conclude with `this` after adjusting the coercions. Establish `hr2 : 2 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega`. Establish `hr1 : (1 : ℝ) ≤ D.R.r` using `by exact_mod_cast (by omega : 1 ≤ D.R.r)`. Establish `hDe : (placeRankTwoOne.dimY D : ℝ) = (T.Dp : ℝ)`. Establish `: placeRankTwoOne.dimY D = T.Dp` using `by rw [T.Dp_eq]; rfl`.

Conclude with `this` after adjusting the coercions. Establish `hD1 : (1 : ℝ) ≤ (T.Dp : ℝ)`. Establish `: 1 ≤ T.Dp`. Rewrite using `[T.Dp_eq]`. Establish `h1 : 0 < D.R.r.choose 2` using `Nat.choose_pos hr2`.

Establish `h2 : 0 < D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Conclude with `Nat.mul_pos h2 h1`. Conclude with `this` after adjusting the coercions. Establish `hZ1 : (1 : ℝ) ≤ zBase L`. Unfold `zBase`.

Establish `: (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hP1 : 1 ≤ T.PP`. Rewrite using `[T.PP_eq]`. Establish `h1` using `Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)`.

Establish `h2` using `T.one_le_CP`. Use the polynomial consequences of the given equalities and inequalities. Use `set p : ℝ := placeRankTwoOne.PP D L CP AP with hp`. Establish `hxCp : 1 ≤ L.sc.x ^ T.Cp` using `Real.one_le_rpow hx1.le T.Cp_nonneg`. Establish `hTTr : placeRankTwoOne.PP D L CP AP ^ 2 * (placeRankTwoOne.dimY D : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) = p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ)` using `by rw [hDe]`.

Use `⟨placeRankTwoOne.TT_nonneg D L CP AP, placeRankTwoOne.TT_le_nat D L CP AP T.TO ?_⟩` and prove the remaining obligations. Use `le_trans ?_ T.TO_ge` and prove the remaining obligations. Rewrite using `[hTTr]`. Establish `a1 : p ^ 2 ≤ T.PP ^ 4` using `(pow_le_pow_left₀ h0 hPP 2).trans (pow_le_pow_right₀ hP1 (by norm_num))`. Establish `a2 : (T.Dp : ℝ) ^ 2 ≤ (T.Dp : ℝ) ^ 3` using `pow_le_pow_right₀ hD1 (by norm_num)`.

Establish `a3 : p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k` using `by gcongr`. Establish `a4 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f` using `le_mul_of_one_le_right (by positivity) hf1`. Establish `a5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp` using `le_mul_of_one_le_right (by positivity) hxCp`. Establish `hd : (D.R.m : ℝ) * L.de2 ≤ D.R.m`. Use `L.thickDensity_le_one` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `div_le_div₀ (by positivity) (a3.trans (a4.trans a5)) (mul_pos (by linarith) L.thickDensity_pos) hd`.
-/
theorem TT_le_TO (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) (CP AP : ℝ)
    (h0 : 0 ≤ placeRankTwoOne.PP D L CP AP) (hPP : placeRankTwoOne.PP D L CP AP ≤ T.PP) :
    0 ≤ placeRankTwoOne.TT D L CP AP ∧ placeRankTwoOne.TT D L CP AP ≤ (T.TO : ℝ) := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hk1 : (1 : ℝ) ≤ D.R.k := by
    have : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ D.R.m := by
    have : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
    exact_mod_cast this
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hr2 : 2 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hr1 : (1 : ℝ) ≤ D.R.r := by exact_mod_cast (by omega : 1 ≤ D.R.r)
  have hDe : (placeRankTwoOne.dimY D : ℝ) = (T.Dp : ℝ) := by
    have : placeRankTwoOne.dimY D = T.Dp := by rw [T.Dp_eq]; rfl
    exact_mod_cast this
  have hD1 : (1 : ℝ) ≤ (T.Dp : ℝ) := by
    have : 1 ≤ T.Dp := by
      rw [T.Dp_eq]
      have h1 : 0 < D.R.r.choose 2 := Nat.choose_pos hr2
      have h2 : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
      exact Nat.mul_pos h2 h1
    exact_mod_cast this
  have hZ1 : (1 : ℝ) ≤ zBase L := by
    unfold zBase
    have : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    nlinarith
  have hP1 : 1 ≤ T.PP := by
    rw [T.PP_eq]
    have h1 := Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)
    have h2 := T.one_le_CP
    nlinarith
  set p : ℝ := placeRankTwoOne.PP D L CP AP with hp
  have hxCp : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow hx1.le T.Cp_nonneg
  have hTTr : placeRankTwoOne.PP D L CP AP ^ 2 * (placeRankTwoOne.dimY D : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) =
      p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) / (D.R.m : ℝ) := by rw [hDe]
  refine ⟨placeRankTwoOne.TT_nonneg D L CP AP, placeRankTwoOne.TT_le_nat D L CP AP T.TO ?_⟩
  refine le_trans ?_ T.TO_ge
  rw [hTTr]
  have a1 : p ^ 2 ≤ T.PP ^ 4 :=
    (pow_le_pow_left₀ h0 hPP 2).trans (pow_le_pow_right₀ hP1 (by norm_num))
  have a2 : (T.Dp : ℝ) ^ 2 ≤ (T.Dp : ℝ) ^ 3 := pow_le_pow_right₀ hD1 (by norm_num)
  have a3 : p ^ 2 * (T.Dp : ℝ) ^ 2 * (D.R.k : ℝ) ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k := by gcongr
  have a4 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k ≤ T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f :=
    le_mul_of_one_le_right (by positivity) hf1
  have a5 : T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f ≤
      T.PP ^ 4 * (T.Dp : ℝ) ^ 3 * D.R.k * D.R.f * L.sc.x ^ T.Cp :=
    le_mul_of_one_le_right (by positivity) hxCp
  have hd : (D.R.m : ℝ) * L.de2 ≤ D.R.m := by
    have := L.thickDensity_le_one; nlinarith
  exact div_le_div₀ (by positivity) (a3.trans (a4.trans a5)) (mul_pos (by linarith) L.thickDensity_pos) hd

/- English proof (translation)
Take `⟨hT0, hTO⟩` from `TT_le_TO D L P T CP AP h0 hPP`. Establish `hDe : (placeRankTwoOne.dimY D : ℝ) = (T.Dp : ℝ)`. Establish `: placeRankTwoOne.dimY D = T.Dp` using `by rw [T.Dp_eq]; rfl`. Conclude with `this` after adjusting the coercions. Establish `hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ)`.

Establish `: D.R.r ≤ D.R.N D.R.m`. Unfold `Ranks.r Ranks.N`. Establish `h1 : D.R.m ≤ D.R.m * (D.R.t + 1)` using `Nat.le_mul_of_pos_right _ (Nat.succ_pos _)`. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions.

Establish `hr0 : (0 : ℝ) ≤ (D.R.r : ℝ)` using `Nat.cast_nonneg _`. Establish `hd0 : (0 : ℝ) ≤ (T.Dp : ℝ)` using `Nat.cast_nonneg _`. Establish `ht0 : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Unfold `placeRankTwoOne.Gc`. Rewrite using `[hDe]`.

Generalize the expression as in `placeRankTwoOne.TT D L CP AP = tt at hT0 hTO`. Prove the components needed by the constructor for the conclusion. Establish `g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤ ((T.TO : ℝ) + T.Dp + 2) * ((T.TO : ℝ) + T.Dp + 2 + 2 * (D.R.N D.R.m : ℝ))` using `mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)`. Establish `g2` using `T.Del_gap`. Establish `g3 : (1 : ℝ) ≤ (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ))` using `by nlinarith`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `q1 : 40 * ((T.Dp : ℝ) + 2) ≤ (T.TO : ℝ)` using `by exact_mod_cast T.TO_40`. Establish `q2 : 2 * (D.R.r : ℝ) ≤ (T.TO : ℝ)`. Conclude with `le_trans (Nat.le_add_left _ _) T.TO_nW` after adjusting the coercions. Establish `g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤ (41 / 40 * (T.TO : ℝ)) * (81 / 40 * (T.TO : ℝ))` using `mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)`.

Establish `q3 : (80 : ℝ) ≤ (T.TO : ℝ)` using `by linarith`. Establish `q4` using `T.heightBound_ge_order_sq`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem Gc_le (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) (CP AP : ℝ)
    (h0 : 0 ≤ placeRankTwoOne.PP D L CP AP) (hPP : placeRankTwoOne.PP D L CP AP ≤ T.PP) :
    placeRankTwoOne.Gc D L CP AP + 1 ≤ 4 * ((D.s.Del : ℚ) : ℝ) ∧ placeRankTwoOne.Gc D L CP AP + 1 ≤ LevelStarExponents.h0 L := by
  obtain ⟨hT0, hTO⟩ := TT_le_TO D L P T CP AP h0 hPP
  have hDe : (placeRankTwoOne.dimY D : ℝ) = (T.Dp : ℝ) := by
    have : placeRankTwoOne.dimY D = T.Dp := by rw [T.Dp_eq]; rfl
    exact_mod_cast this
  have hrN : (D.R.r : ℝ) ≤ (D.R.N D.R.m : ℝ) := by
    have : D.R.r ≤ D.R.N D.R.m := by
      unfold Ranks.r Ranks.N
      have h1 : D.R.m ≤ D.R.m * (D.R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
      omega
    exact_mod_cast this
  have hr0 : (0 : ℝ) ≤ (D.R.r : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (T.Dp : ℝ) := Nat.cast_nonneg _
  have ht0 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  unfold placeRankTwoOne.Gc
  rw [hDe]
  generalize placeRankTwoOne.TT D L CP AP = tt at hT0 hTO
  constructor
  · have g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        ((T.TO : ℝ) + T.Dp + 2) * ((T.TO : ℝ) + T.Dp + 2 + 2 * (D.R.N D.R.m : ℝ)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have g2 := T.Del_gap
    have g3 : (1 : ℝ) ≤ (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) := by nlinarith
    linarith
  · have q1 : 40 * ((T.Dp : ℝ) + 2) ≤ (T.TO : ℝ) := by exact_mod_cast T.TO_40
    have q2 : 2 * (D.R.r : ℝ) ≤ (T.TO : ℝ) := by
      exact_mod_cast le_trans (Nat.le_add_left _ _) T.TO_nW
    have g1 : (tt + T.Dp + 2) * (tt + T.Dp + 2 + 2 * (D.R.r : ℝ)) ≤
        (41 / 40 * (T.TO : ℝ)) * (81 / 40 * (T.TO : ℝ)) :=
      mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have q3 : (80 : ℝ) ≤ (T.TO : ℝ) := by linarith
    have q4 := T.heightBound_ge_order_sq
    nlinarith

section Clauses

variable (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (hK : DV.KapDef D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)

include P hK h1 h2

/- English proof (translation)
Establish `hp : (D.R.sigW j).1 = D.R.k + j - 1` using `rfl`. Rewrite using `[kapW_big D hK j h1 h2 τ i (by omega), sgR_cloud D τ i.1 hi]`. Take `⟨v0, v1⟩` from `L.cloud_v τ ⟨i.1, hi⟩`. Establish `c1 : (i.1 : ℝ) + 2 ≤ D.R.k` using `by exact_mod_cast (by omega : i.1 + 2 ≤ D.R.k)`. Establish `c2 : (1 : ℝ) ≤ j` using `by exact_mod_cast h1`.

Establish `c3 : (j : ℝ) ≤ D.R.m` using `by exact_mod_cast h2`. Establish `c4 : (0 : ℝ) ≤ (i.1 : ℝ)` using `Nat.cast_nonneg _`. Establish `c5 : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Establish `hX : (D.R.r : ℝ) + D.R.t ≤ Cn * ((D.R.r : ℝ) + D.R.t)` using `le_mul_of_one_le_left (by positivity) hCn`. Rewrite `hX`, the goal using `[r_cast]`.

Apply the tactic sequence `constructor <;> linarith`.
-/
theorem cloud_entries_bound_of (Cn : ℝ) (hCn : 1 ≤ Cn) (τ : D.what₂.Tau) (i : Fin D.R.r) (hi : i.1 < D.R.k - 1) :
    -(Cn * ((D.R.r : ℝ) + D.R.t)) ≤ (DV.kapW D j τ i : ℝ) - DV.wSz D j τ ∧
      (DV.kapW D j τ i : ℝ) - DV.wSz D j τ ≤ L.Sc + Cn * ((D.R.r : ℝ) + D.R.t) := by
  have hp : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  rw [kapW_big D hK j h1 h2 τ i (by omega), sgR_cloud D τ i.1 hi]
  obtain ⟨v0, v1⟩ := L.cloud_v τ ⟨i.1, hi⟩
  have c1 : (i.1 : ℝ) + 2 ≤ D.R.k := by exact_mod_cast (by omega : i.1 + 2 ≤ D.R.k)
  have c2 : (1 : ℝ) ≤ j := by exact_mod_cast h1
  have c3 : (j : ℝ) ≤ D.R.m := by exact_mod_cast h2
  have c4 : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
  have c5 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hX : (D.R.r : ℝ) + D.R.t ≤ Cn * ((D.R.r : ℝ) + D.R.t) :=
    le_mul_of_one_le_left (by positivity) hCn
  rw [r_cast] at hX ⊢
  constructor <;> linarith

/- English proof (translation)
The claim follows from `|(DV.kapW D j τ i : ℝ)| ≤ L.etaSz + L.Sc + Cn * ((D.R.r : ℝ) + D.R.t) := by have hp : (D.R.sigW j).1 = D.R.k + j - 1 := rfl have hr : D.R.r = D.R.k + D.R.m - 1 := rfl have hk := D.R.m_add_three_le_k obtain ⟨a1, a2⟩ := abs_le.1 (sgR_be D L j h1 h2 τ i.1 hi i.2) have c1 : (D.R.k : …`.
-/
theorem low_entries_bound_of (Cn : ℝ) (hCn : 1 ≤ Cn) (τ : D.what₂.Tau) (i : Fin D.R.r) (hi : D.R.k - 1 ≤ i.1) :
    |(DV.kapW D j τ i : ℝ)| ≤ L.etaSz + L.Sc + Cn * ((D.R.r : ℝ) + D.R.t) := by
  have hp : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  obtain ⟨a1, a2⟩ := abs_le.1 (sgR_be D L j h1 h2 τ i.1 hi i.2)
  have c1 : (D.R.k : ℝ) ≤ (i.1 : ℝ) + 1 := by exact_mod_cast (by omega : D.R.k ≤ i.1 + 1)
  have c2 : (1 : ℝ) ≤ j := by exact_mod_cast h1
  have c3 : (j : ℝ) ≤ D.R.m := by exact_mod_cast h2
  have c5 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have c6 : (i.1 : ℝ) + 2 ≤ (D.R.k : ℝ) + D.R.m := by
    exact_mod_cast (by have := i.2; omega : i.1 + 2 ≤ D.R.k + D.R.m)
  have c7 : (5 : ℝ) ≤ D.R.k := by
    exact_mod_cast (by have := D.R.two_le_m; omega : 5 ≤ D.R.k)
  have hS := L.Sc_pos
  have hX : (D.R.r : ℝ) + D.R.t ≤ Cn * ((D.R.r : ℝ) + D.R.t) :=
    le_mul_of_one_le_left (by positivity) hCn
  rw [r_cast] at hX ⊢
  by_cases hb : i.1 < (D.R.sigW j).1
  · rw [kapW_big D hK j h1 h2 τ i hb, abs_le]
    have c8 : (i.1 : ℝ) + 2 ≤ (D.R.k : ℝ) + j := by exact_mod_cast (by omega : i.1 + 2 ≤ D.R.k + j)
    constructor <;> linarith
  · rw [kapW_small D hK j h1 h2 τ i (by omega), abs_le]
    have c8 : (D.R.k : ℝ) + j ≤ (i.1 : ℝ) + 1 := by exact_mod_cast (by omega : D.R.k + j ≤ i.1 + 1)
    constructor <;> linarith

/- English proof (translation)
Establish `hp : (D.R.sigW j).1 = D.R.k + j - 1` using `rfl`. Establish `hr : D.R.r = D.R.k + D.R.m - 1` using `rfl`. Establish `hk` using `D.R.m_add_three_le_k`. Establish `h6` using `six_le_h0 D L P`. Establish `hD : (0 : ℝ) ≤ 4 * ((D.s.Del : ℚ) : ℝ)`.

Establish `: (0 : ℝ) < ((D.s.Del : ℚ) : ℝ)` using `by exact_mod_cast D.s.Del_pos`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `st : ∀ a, 0 ≤ a → a + 1 < D.R.r → (0 : ℝ) ≤ sgR D τ a - sgR D τ (a + 1)` using `fun a _ ha => sgR_step D L P τ 0 hD (by linarith) (fun hm => le_trans (by linarith) (minimalGap_le_first_lowerRowParameter D L P j h1 h2 τ hw hm)) a ha`. Take `⟨p', hp'⟩ : ∃ p', (D.R.sigW j).1 = p' + 1` from `⟨D.R.k + j - 2, by omega⟩`. Establish `s1` using `steps_sum (sgR D τ) 0 D.R.r 0 st i.1 (Nat.zero_le _) p' (by omega) (by have := l.2; omega)`.

Establish `s2` using `sgR_step_low D L P τ p' (by omega) (by have := l.2; omega)`. Establish `s3` using `steps_sum (sgR D τ) 0 D.R.r 0 st (p' + 1) (Nat.zero_le _) l.1 (by omega) l.2`. Rewrite using `[kapW_sub_bar D hK j h1 h2 τ i l hi hl]`. Establish `c4 : (0 : ℝ) ≤ (i.1 : ℝ)` using `Nat.cast_nonneg _`. Establish `c6 : (l.1 : ℝ) + 2 ≤ (D.R.k : ℝ) + D.R.m`.

Conclude with `(by have := l.2; omega : l.1 + 2 ≤ D.R.k + D.R.m)` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem noncompact_gaps_of (τ : D.what₂.Tau) (hw : L.sc.w'' D.R.n ≤ DV.wSz D j τ) (i l : Fin D.R.r)
    (hi : i.1 < (D.R.sigW j).1) (hl : (D.R.sigW j).1 ≤ l.1) :
    LevelStarExponents.h0 L ≤ (DV.kapW D j τ i : ℝ) - DV.kapW D j τ l := by
  have hp : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have hk := D.R.m_add_three_le_k
  have h6 := six_le_h0 D L P
  have hD : (0 : ℝ) ≤ 4 * ((D.s.Del : ℚ) : ℝ) := by
    have : (0 : ℝ) < ((D.s.Del : ℚ) : ℝ) := by exact_mod_cast D.s.Del_pos
    linarith
  have st : ∀ a, 0 ≤ a → a + 1 < D.R.r → (0 : ℝ) ≤ sgR D τ a - sgR D τ (a + 1) := fun a _ ha =>
    sgR_step D L P τ 0 hD (by linarith) (fun hm => le_trans (by linarith) (minimalGap_le_first_lowerRowParameter D L P j h1 h2 τ hw hm)) a ha
  obtain ⟨p', hp'⟩ : ∃ p', (D.R.sigW j).1 = p' + 1 := ⟨D.R.k + j - 2, by omega⟩
  have s1 := steps_sum (sgR D τ) 0 D.R.r 0 st i.1 (Nat.zero_le _) p' (by omega) (by have := l.2; omega)
  have s2 := sgR_step_low D L P τ p' (by omega) (by have := l.2; omega)
  have s3 := steps_sum (sgR D τ) 0 D.R.r 0 st (p' + 1) (Nat.zero_le _) l.1 (by omega) l.2
  rw [kapW_sub_bar D hK j h1 h2 τ i l hi hl]
  have c4 : (0 : ℝ) ≤ (i.1 : ℝ) := Nat.cast_nonneg _
  have c6 : (l.1 : ℝ) + 2 ≤ (D.R.k : ℝ) + D.R.m := by
    exact_mod_cast (by have := l.2; omega : l.1 + 2 ≤ D.R.k + D.R.m)
  linarith

/- English proof (translation)
Establish `h6` using `six_le_h0 D L P`. Establish `s1` using `steps_sum (sgR D τ) (D.R.k - 1) D.R.r (LevelStarExponents.h0 L) (fun a ha ha' => sgR_step_low D L P τ a ha ha') i.1 hi i'.1 hlt.le i'.2`. Rewrite using `[kapW_sub_same D hK j h1 h2 τ i i' hb]`. Establish `c : (1 : ℝ) ≤ (i'.1 : ℝ) - i.1`. Establish `: (i.1 : ℝ) + 1 ≤ (i'.1 : ℝ)` using `by exact_mod_cast hlt`.

Combine the linear equalities and inequalities to obtain the conclusion. Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 c) (by linarith : (0 : ℝ) ≤ LevelStarExponents.h0 L - 1)]`.
-/
theorem low_entries_apart_of_lt (τ : D.what₂.Tau) (i i' : Fin D.R.r) (hi : D.R.k - 1 ≤ i.1) (hlt : i.1 < i'.1)
    (hb : i.1 < (D.R.sigW j).1 ↔ i'.1 < (D.R.sigW j).1) :
    LevelStarExponents.h0 L - 1 ≤ (DV.kapW D j τ i : ℝ) - DV.kapW D j τ i' := by
  have h6 := six_le_h0 D L P
  have s1 := steps_sum (sgR D τ) (D.R.k - 1) D.R.r (LevelStarExponents.h0 L) (fun a ha ha' => sgR_step_low D L P τ a ha ha') i.1 hi i'.1
    hlt.le i'.2
  rw [kapW_sub_same D hK j h1 h2 τ i i' hb]
  have c : (1 : ℝ) ≤ (i'.1 : ℝ) - i.1 := by
    have : (i.1 : ℝ) + 1 ≤ (i'.1 : ℝ) := by exact_mod_cast hlt
    linarith
  nlinarith [mul_nonneg (sub_nonneg.2 c) (by linarith : (0 : ℝ) ≤ LevelStarExponents.h0 L - 1)]

/- English proof (translation)
Break down `Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h` into its components or cases. Conclude with `le_trans (low_entries_apart_of_lt D L P hK j h1 h2 τ i i' hi h hb) (le_abs_self _)`. Rewrite using `[abs_sub_comm]`. Conclude with `le_trans (low_entries_apart_of_lt D L P hK j h1 h2 τ i' i hi' h hb.symm) (le_abs_self _)`.
-/
theorem low_entries_apart_of (τ : D.what₂.Tau) (i i' : Fin D.R.r) (hi : D.R.k - 1 ≤ i.1) (hi' : D.R.k - 1 ≤ i'.1) (hne : i ≠ i')
    (hb : i.1 < (D.R.sigW j).1 ↔ i'.1 < (D.R.sigW j).1) :
    LevelStarExponents.h0 L - 1 ≤ |(DV.kapW D j τ i : ℝ) - DV.kapW D j τ i'| := by
  rcases Nat.lt_or_gt_of_ne (fun h => hne (Fin.ext h)) with h | h
  · exact le_trans (low_entries_apart_of_lt D L P hK j h1 h2 τ i i' hi h hb) (le_abs_self _)
  · rw [abs_sub_comm]
    exact le_trans (low_entries_apart_of_lt D L P hK j h1 h2 τ i' i hi' h hb.symm) (le_abs_self _)

/- English proof (translation)
Take `⟨g1, g2⟩` from `Gc_le D L P T CP AP h0 hPP`. Establish `s` using `sgR_step D L P τ (placeRankTwoOne.Gc D L CP AP + 1) g1 g2 (fun hm => le_trans g2 (minimalGap_le_first_lowerRowParameter D L P j h1 h2 τ hw hm)) i.1 (by have := i'.2; omega)`. Rewrite using `[kapW_sub_same D hK j h1 h2 τ i i' (by omega), hs]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem consecutive_entries_gap_of (T : ParamsT D L P) (CP AP : ℝ) (h0 : 0 ≤ placeRankTwoOne.PP D L CP AP) (hPP : placeRankTwoOne.PP D L CP AP ≤ T.PP)
    (τ : D.what₂.Tau) (hw : L.sc.w'' D.R.n ≤ DV.wSz D j τ) (i i' : Fin D.R.r) (hs : i'.1 = i.1 + 1)
    (hne : i'.1 ≠ (D.R.sigW j).1) :
    placeRankTwoOne.Gc D L CP AP ≤ (DV.kapW D j τ i : ℝ) - DV.kapW D j τ i' := by
  obtain ⟨g1, g2⟩ := Gc_le D L P T CP AP h0 hPP
  have s := sgR_step D L P τ (placeRankTwoOne.Gc D L CP AP + 1) g1 g2
    (fun hm => le_trans g2 (minimalGap_le_first_lowerRowParameter D L P j h1 h2 τ hw hm)) i.1 (by have := i'.2; omega)
  rw [kapW_sub_same D hK j h1 h2 τ i i' (by omega), hs]
  push_cast
  linarith

end Clauses

/- English proof (translation)
Establish `hx1 : 1 < L.sc.x` using `L.sc.one_lt_alt`. Establish `hL1 : 1 ≤ L.sc.L` using `by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le`. Establish `hf1 : (1 : ℝ) ≤ D.R.f`. Establish `: 1 ≤ D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Conclude with `this` after adjusting the coercions.

Establish `hr1 : (1 : ℝ) ≤ D.R.r`. Establish `: 1 ≤ D.R.r` using `by unfold Ranks.r; have := D.R.two_le_m; omega`. Conclude with `this` after adjusting the coercions. Establish `hZ1 : (1 : ℝ) ≤ zBase L`. Unfold `zBase`.

Establish `: (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[T.PP_eq]`. Establish `h1` using `Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)`. Establish `h2` using `T.one_le_CP`.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem one_le_parPP (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) : 1 ≤ T.PP := by
  have hx1 : 1 < L.sc.x := L.sc.one_lt_alt
  have hL1 : 1 ≤ L.sc.L := by unfold Scale.L; exact Real.one_le_rpow hx1.le L.sc.eps_pos.le
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
    exact_mod_cast this
  have hr1 : (1 : ℝ) ≤ D.R.r := by
    have : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
    exact_mod_cast this
  have hZ1 : (1 : ℝ) ≤ zBase L := by
    unfold zBase
    have : (1 : ℝ) ≤ (D.R.f : ℝ) * D.R.r := by nlinarith
    nlinarith
  rw [T.PP_eq]
  have h1 := Real.one_le_rpow hZ1 (by linarith [T.eP_ge] : 0 ≤ T.eP)
  have h2 := T.one_le_CP
  nlinarith

/- English proof (translation)
Use `le_trans ?_ T.nW_lo.1` and prove the remaining obligations. Establish `hf : 0 < D.R.f` using `by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega`. Establish `hr : 0 < D.R.r` using `by unfold Ranks.r; have := D.R.two_le_m; omega`. Conclude with `Nat.mul_pos (Nat.mul_pos hf hr) (Nat.succ_pos _)`.
-/
theorem one_le_nWn (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) : 1 ≤ T.nWn := by
  refine le_trans ?_ T.nW_lo.1
  have hf : 0 < D.R.f := by unfold Ranks.f Ranks.n; have := D.R.ord_pos; omega
  have hr : 0 < D.R.r := by unfold Ranks.r; have := D.R.two_le_m; omega
  exact Nat.mul_pos (Nat.mul_pos hf hr) (Nat.succ_pos _)

/- English proof (translation)
Establish `hEta : Formalism.MainNotions.SizeEta L` using `hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1`. Establish `hwin` using `wI_win_of D L Cs hSz hEta j h1 h2`. Establish `hw : ∀ τ, L.sc.w'' D.R.n ≤ DV.wSz D j τ` using `fun τ => by rw [← wI_cast_h]; exact (hwin τ).1`. Establish `h6` using `six_le_h0 D L P`. Establish `ht : placeRankTwoOne.PP D L CP AP ≤ 2 * D.R.t`.

Use `PP_le_t_of_split D L P T CP AP hPP (one_le_parPP D L P T) (one_le_nWn D L P T)` as an intermediate fact. Establish `h3 : (0 : ℝ) ≤ (D.R.t : ℝ)` using `Nat.cast_nonneg _`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨p1, p2, p3, p4, p5⟩` from `size_parameter_bounds_of D L P T CP AP h0 hPP hCb`. Take `⟨q1, q2, q3, q4, q5, q6⟩` from `size_tail_bounds_of D L P hS Cn Cq hCn hCq`.

Use `⟨h1, h2, ?_, ?_, ?_, hwin, size_product_bound_of D L CP AP ht hS hx4 hy, ?_, ?_, ?_, p1, p2, p3, p4, p5, q1, q2, q3, q4, q5, q6, hCP3, hZ, hAP, P, T, hS, hPP, (TT_le_TO D L P T CP AP h0 hPP).2⟩` and prove the remaining obligations. Introduce `τ i hi`. Rewrite using `[wI_cast_h]`. Conclude with `cloud_entries_bound_of D L P hK j h1 h2 Cn hCn1 τ i hi`. Introduce `τ i hi`.

Conclude with `low_entries_bound_of D L P hK j h1 h2 Cn hCn1 τ i hi`. Introduce `τ i l hi hl`. Use `noncompact_gaps_of D L P hK j h1 h2 τ (hw τ) i l hi hl` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `τ i i' hs hne`.

Conclude with `consecutive_entries_gap_of D L P hK j h1 h2 T CP AP h0 hPP τ (hw τ) i i' hs hne`. Introduce `τ i i' hi hi' hne hb`. Conclude with `low_entries_apart_of D L P hK j h1 h2 τ i i' hi hi' hne hb`. Introduce `τ i l hi hl`. Conclude with `noncompact_gaps_of D L P hK j h1 h2 τ (hw τ) i l hi hl`.
-/
theorem size_setting_of_bounds (D : D7) (L : SizeData₂ D) (P : ParameterChoice' D L) (T : ParamsT D L P) (hS : Formalism.MainNotions.SizesAt L)
    (hK : DV.KapDef D) (Cs : ℝ) (hSz : placeRankTwoOne.Sizes D L Cs) (Cn CP AP Cq : ℝ) (hCn : P.CYL + 1 ≤ Cn) (hCn1 : 1 ≤ Cn)
    (h0 : 0 ≤ placeRankTwoOne.PP D L CP AP) (hPP : placeRankTwoOne.PP D L CP AP ≤ T.PP) (hCb : L.Ct ≤ T.Cb) (hCq : Cq ≤ 2 * L.Ct + 5)
    (hCP3 : 10 ^ 3 ≤ CP) (hZ : CP ^ 20 ≤ zBase L) (hAP : 12 ≤ AP) (hx4 : 4 ≤ L.sc.x) (hy : 3 ≤ L.sc.x ^ (L.sc.eps / 4)) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) :
    placeRankTwoOne.SizeSettingLemmaThree D L Cn CP AP Cq j (placeRankTwoOne.wI D j) := by
  have hEta : Formalism.MainNotions.SizeEta L := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hwin := wI_win_of D L Cs hSz hEta j h1 h2
  have hw : ∀ τ, L.sc.w'' D.R.n ≤ DV.wSz D j τ := fun τ => by rw [← wI_cast_h]; exact (hwin τ).1
  have h6 := six_le_h0 D L P
  have ht : placeRankTwoOne.PP D L CP AP ≤ 2 * D.R.t := by
    have := PP_le_t_of_split D L P T CP AP hPP (one_le_parPP D L P T) (one_le_nWn D L P T)
    have h3 : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  obtain ⟨p1, p2, p3, p4, p5⟩ := size_parameter_bounds_of D L P T CP AP h0 hPP hCb
  obtain ⟨q1, q2, q3, q4, q5, q6⟩ := size_tail_bounds_of D L P hS Cn Cq hCn hCq
  refine ⟨h1, h2, ?_, ?_, ?_, hwin, size_product_bound_of D L CP AP ht hS hx4 hy, ?_, ?_, ?_, p1, p2, p3, p4, p5, q1, q2, q3, q4, q5, q6, hCP3, hZ, hAP,
    P, T, hS, hPP, (TT_le_TO D L P T CP AP h0 hPP).2⟩
  · intro τ i hi
    rw [wI_cast_h]
    exact cloud_entries_bound_of D L P hK j h1 h2 Cn hCn1 τ i hi
  · intro τ i hi
    exact low_entries_bound_of D L P hK j h1 h2 Cn hCn1 τ i hi
  · intro τ i l hi hl
    have := noncompact_gaps_of D L P hK j h1 h2 τ (hw τ) i l hi hl
    linarith
  · intro τ i i' hs hne
    exact consecutive_entries_gap_of D L P hK j h1 h2 T CP AP h0 hPP τ (hw τ) i i' hs hne
  · intro τ i i' hi hi' hne hb
    exact low_entries_apart_of D L P hK j h1 h2 τ i i' hi hi' hne hb
  · intro τ i l hi hl
    exact noncompact_gaps_of D L P hK j h1 h2 τ (hw τ) i l hi hl

/- English proof (translation)
Take `⟨xs, hs⟩` from `sizes_family_eventually Fm hTu`. Establish `he : 0 < eps`. Take `⟨i⟩` from `Fm.Ix_zero`. Rewrite using `[← Fm.L_eps 0 i]`. Conclude with `(Fm.L 0 i).sc.eps_pos`.

Use `⟨max xs (max (Fm.x1 + 1) (max 4 (max ((3 : ℝ) ^ (4 / eps)) ((CP ^ 20) ^ (1 / eps))))), fun x hx i hK j h1 h2 => ?_⟩` and prove the remaining obligations. Establish `a1 : xs ≤ x` using `le_trans (le_max_left _ _) hx`. Establish `hx'` using `le_trans (le_max_right _ _) hx`. Establish `a2 : Fm.x1 < x` using `lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_left _ _) hx')`. Establish `hx''` using `le_trans (le_max_right _ _) hx'`.

Establish `a3 : 4 ≤ x` using `le_trans (le_max_left _ _) hx''`. Establish `hx'''` using `le_trans (le_max_right _ _) hx''`. Establish `a4 : (3 : ℝ) ^ (4 / eps) ≤ x` using `le_trans (le_max_left _ _) hx'''`. Establish `a5 : (CP ^ 20) ^ (1 / eps) ≤ x` using `le_trans (le_max_right _ _) hx'''`. Establish `hZ : CP ^ 20 ≤ zBase (Fm.L x i)`.

Establish `hC0 : (0 : ℝ) ≤ CP ^ 20` using `by positivity`. Establish `e1 : CP ^ 20 = ((CP ^ 20) ^ (1 / eps)) ^ eps`. Rewrite using `[← Real.rpow_mul hC0, one_div, inv_mul_cancel₀ he.ne', Real.rpow_one]`. Establish `e2 : ((CP ^ 20) ^ (1 / eps)) ^ eps ≤ x ^ eps` using `Real.rpow_le_rpow (Real.rpow_nonneg hC0 _) a5 he.le`. Establish `hL : (Fm.L x i).sc.L = x ^ eps`.

Unfold `Scale.L`. Rewrite using `[Fm.L_x x i a2, Fm.L_eps x i]`. Establish `hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f`. Establish `: 1 ≤ (Fm.D x i).R.f`. Unfold `Ranks.f Ranks.n`.

Use `(Fm.D x i).R.ord_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions. Establish `hr1 : (1 : ℝ) ≤ (Fm.D x i).R.r`. Establish `: 1 ≤ (Fm.D x i).R.r`.

Unfold `Ranks.r`. Use `(Fm.D x i).R.m_add_three_le_k` as an intermediate fact. Use `(Fm.D x i).R.two_le_m` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Conclude with `this` after adjusting the coercions.

Establish `hxe : 0 ≤ x ^ eps` using `Real.rpow_nonneg (by linarith) _`. Establish `hfr : (1 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r` using `by nlinarith`. Unfold `zBase`. Rewrite using `[hL]`. Combine the equalities or inequalities in the displayed calculation.

Use `size_setting_of_bounds _ _ (Fm.params x a2 i) (Fm.parT x a2 i) (Fm.sizes x a2 i) hK _ (hs x a1 a2 i) _ CP AP Cq ?_ ?_ (h0 x a2 i) (hPP x a2 i) ?_ ?_ hCP3 hZ hAP ?_ ?_ j h1 h2` and prove the remaining obligations. Rewrite using `[Fm.params_CYL x a2 i]`. Use `CYL_nonneg Fm` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Fm.Ct_eq x i, Fm.parT_Cb x a2 i]`.

Conclude with `hCb`. Rewrite using `[Fm.Ct_eq x i]`. Conclude with `hCq`. Rewrite using `[Fm.L_x x i a2]`. Conclude with `a3`.

Rewrite using `[Fm.L_x x i a2, Fm.L_eps x i]`. Establish `h3 : ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) = 3`. Rewrite using `[← Real.rpow_mul (by norm_num)]`. Establish `: 4 / eps * (eps / 4) = 1` using `by field_simp`. Rewrite using `[this, Real.rpow_one]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem size_settings_family_of {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hTu : Formalism.MainNotions.TuSize Fm) (CP AP Cq : ℝ)
    (h0 : ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), 0 ≤ placeRankTwoOne.PP (Fm.D x i) (Fm.L x i) CP AP)
    (hPP : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), placeRankTwoOne.PP (Fm.D x i) (Fm.L x i) CP AP ≤ (Fm.parT x hx i).PP)
    (hCq : Cq ≤ 2 * Fm.Ct + 5) (hCb : Fm.Ct ≤ Fm.Cb) (hCP3 : 10 ^ 3 ≤ CP) (hAP : 12 ≤ AP) :
    placeRankTwoOne.SlopeSettingFamily Fm (Fm.CYL + 1) CP AP Cq := by
  obtain ⟨xs, hs⟩ := sizes_family_eventually Fm hTu
  have he : 0 < eps := by
    obtain ⟨i⟩ := Fm.Ix_zero
    rw [← Fm.L_eps 0 i]; exact (Fm.L 0 i).sc.eps_pos
  refine ⟨max xs (max (Fm.x1 + 1) (max 4 (max ((3 : ℝ) ^ (4 / eps)) ((CP ^ 20) ^ (1 / eps))))),
    fun x hx i hK j h1 h2 => ?_⟩
  have a1 : xs ≤ x := le_trans (le_max_left _ _) hx
  have hx' := le_trans (le_max_right _ _) hx
  have a2 : Fm.x1 < x := lt_of_lt_of_le (lt_add_one _) (le_trans (le_max_left _ _) hx')
  have hx'' := le_trans (le_max_right _ _) hx'
  have a3 : 4 ≤ x := le_trans (le_max_left _ _) hx''
  have hx''' := le_trans (le_max_right _ _) hx''
  have a4 : (3 : ℝ) ^ (4 / eps) ≤ x := le_trans (le_max_left _ _) hx'''
  have a5 : (CP ^ 20) ^ (1 / eps) ≤ x := le_trans (le_max_right _ _) hx'''
  have hZ : CP ^ 20 ≤ zBase (Fm.L x i) := by
    have hC0 : (0 : ℝ) ≤ CP ^ 20 := by positivity
    have e1 : CP ^ 20 = ((CP ^ 20) ^ (1 / eps)) ^ eps := by
      rw [← Real.rpow_mul hC0, one_div, inv_mul_cancel₀ he.ne', Real.rpow_one]
    have e2 : ((CP ^ 20) ^ (1 / eps)) ^ eps ≤ x ^ eps :=
      Real.rpow_le_rpow (Real.rpow_nonneg hC0 _) a5 he.le
    have hL : (Fm.L x i).sc.L = x ^ eps := by
      unfold Scale.L; rw [Fm.L_x x i a2, Fm.L_eps x i]
    have hf1 : (1 : ℝ) ≤ (Fm.D x i).R.f := by
      have : 1 ≤ (Fm.D x i).R.f := by
        unfold Ranks.f Ranks.n; have := (Fm.D x i).R.ord_pos; omega
      exact_mod_cast this
    have hr1 : (1 : ℝ) ≤ (Fm.D x i).R.r := by
      have : 1 ≤ (Fm.D x i).R.r := by
        unfold Ranks.r; have := (Fm.D x i).R.m_add_three_le_k; have := (Fm.D x i).R.two_le_m; omega
      exact_mod_cast this
    have hxe : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
    have hfr : (1 : ℝ) ≤ ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r := by nlinarith
    unfold zBase; rw [hL]
    calc CP ^ 20 ≤ x ^ eps := e1 ▸ e2
      _ ≤ ((Fm.D x i).R.f : ℝ) * (Fm.D x i).R.r * x ^ eps := le_mul_of_one_le_left hxe hfr
  refine size_setting_of_bounds _ _ (Fm.params x a2 i) (Fm.parT x a2 i) (Fm.sizes x a2 i) hK _ (hs x a1 a2 i) _ CP AP Cq ?_ ?_
    (h0 x a2 i) (hPP x a2 i) ?_ ?_ hCP3 hZ hAP ?_ ?_ j h1 h2
  · rw [Fm.params_CYL x a2 i]
  · have := CYL_nonneg Fm; linarith
  · rw [Fm.Ct_eq x i, Fm.parT_Cb x a2 i]; exact hCb
  · rw [Fm.Ct_eq x i]; exact hCq
  · rw [Fm.L_x x i a2]; exact a3
  · rw [Fm.L_x x i a2, Fm.L_eps x i]
    have h3 : ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) = 3 := by
      rw [← Real.rpow_mul (by norm_num)]
      have : 4 / eps * (eps / 4) = 1 := by field_simp
      rw [this, Real.rpow_one]
    calc (3 : ℝ) = ((3 : ℝ) ^ (4 / eps)) ^ (eps / 4) := h3.symm
      _ ≤ x ^ (eps / 4) := Real.rpow_le_rpow (by positivity) a4 (by positivity)

/- English proof (translation)
Establish `hAP : 12 ≤ Fm.eP`. Take `⟨y, -, hy, -, ⟨i⟩⟩` from `Fm.exists_pt 0`. Rewrite using `[← Fm.parT_eP y hy i]`. Conclude with `(Fm.parT _ _ i).eP_ge`. Establish `e : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), placeRankTwoOne.PP (Fm.D x i) (Fm.L x i) Fm.CP Fm.eP = (Fm.parT x hx i).PP` using `fun x hx i => by`.

Rewrite using `[← Fm.parT_CP x hx i, ← Fm.parT_eP x hx i]`. Conclude with `placeRankTwoOne.PP_eq_par _`. Use `size_settings_family_of Fm hTu _ _ Cq (fun x hx i => ?_) (fun x hx i => (e x hx i).le) hCq hCb hCP3 hAP` and prove the remaining obligations. Rewrite using `[e x hx i]`. Use `one_le_parPP _ _ _ (Fm.parT x hx i)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem size_settings_family_of_constants {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (hTu : Formalism.MainNotions.TuSize Fm) (Cq : ℝ)
    (hCq : Cq ≤ 2 * Fm.Ct + 5) (hCb : Fm.Ct ≤ Fm.Cb) (hCP3 : 10 ^ 3 ≤ Fm.CP) :
    placeRankTwoOne.SlopeSettingFamily Fm (Fm.CYL + 1) Fm.CP Fm.eP Cq := by
  have hAP : 12 ≤ Fm.eP := by
    obtain ⟨y, -, hy, -, ⟨i⟩⟩ := Fm.exists_pt 0
    rw [← Fm.parT_eP y hy i]; exact (Fm.parT _ _ i).eP_ge
  have e : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x),
      placeRankTwoOne.PP (Fm.D x i) (Fm.L x i) Fm.CP Fm.eP = (Fm.parT x hx i).PP := fun x hx i => by
    rw [← Fm.parT_CP x hx i, ← Fm.parT_eP x hx i]
    exact placeRankTwoOne.PP_eq_par _
  refine size_settings_family_of Fm hTu _ _ Cq (fun x hx i => ?_) (fun x hx i => (e x hx i).le) hCq hCb hCP3 hAP
  rw [e x hx i]
  have := one_le_parPP _ _ _ (Fm.parT x hx i)
  linarith

/- English proof (translation)
Use `⟨hpre.trans (h.1 Fm.CP (by delta Formalism.MainNotions.FamP.cPre; simp)), ?_⟩` and prove the remaining obligations. Establish `h2` using `h.2.2.2 Fm.Cb (by delta Formalism.MainNotions.FamP.cLast; simp)`. Conclude with `(hlast _).trans h2`.
-/
theorem own_bounds_of_Large {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (K : Formalism.MainNotions.TransportedAlt) (CH : ℝ) (h : Fm.Large K CH)
    (hpre : 10 ^ 3 ≤ K.pre) (hlast : ∀ l : List ℝ, l.getD 0 0 ≤ K.last l) : 10 ^ 3 ≤ Fm.CP ∧ Fm.Ct ≤ Fm.Cb := by
  refine ⟨hpre.trans (h.1 Fm.CP (by delta Formalism.MainNotions.FamP.cPre; simp)), ?_⟩
  have h2 := h.2.2.2 Fm.Cb (by delta Formalism.MainNotions.FamP.cLast; simp)
  exact (hlast _).trans h2

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_pos, fun _ _ _ => ⟨⟨10 ^ 3, fun _ => 0, fun _ => 0, fun l => l.getD 0 0⟩, fun Fm CH _ hL hTu Cq hCq => let hb := own_bounds_of_Large Fm _ CH hL le_rfl (fun _ => le_rfl) size_settings_family_of_constants Fm hTu Cq hCq hb.2 hb.1⟩⟩`.
-/
theorem size_settings_family_closed (𝒞 : Formalism.MainNotions.FamClass) :
    Formalism.MainNotions.Closed 𝒞 (fun Fm _ => Formalism.MainNotions.TuSize Fm → ∀ Cq : ℝ, Cq ≤ 2 * Fm.Ct + 5 →
      placeRankTwoOne.SlopeSettingFamily Fm (Fm.CYL + 1) Fm.CP Fm.eP Cq) :=
  ⟨1, one_pos, fun _ _ _ => ⟨⟨10 ^ 3, fun _ => 0, fun _ => 0, fun l => l.getD 0 0⟩, fun Fm CH _ hL hTu Cq hCq =>
    let hb := own_bounds_of_Large Fm _ CH hL le_rfl (fun _ => le_rfl)
    size_settings_family_of_constants Fm hTu Cq hCq hb.2 hb.1⟩⟩

end Formalism.MainNotions.DIV

end
