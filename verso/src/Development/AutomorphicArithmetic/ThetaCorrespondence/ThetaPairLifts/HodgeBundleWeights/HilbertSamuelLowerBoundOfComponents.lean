import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightStatementOfPublished
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedBundleDegreeLowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TwistedFlatBundleRanks
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsDegreeParametersBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightStatementOfPrintsStatement

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CovTop.ShortRoad
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `hX h2 hGD hQd hSi hTo hSA hDG hS hF hDe hSh`. Take `⟨Cp, hCp, htw⟩` from `_root_.GlobalTheory.T.twisted_bundle_degree_lower_bound h2`. Establish `hrk` using `_root_.GlobalTheory.T.twisted_flat_bundle_ranks h2`. Establish `hgood` using `_root_.GlobalTheory.T.covering_domain_lattice_regularity h2`. Use `Closed.imp (((((((_root_.GlobalTheory.T.exists_degree_parameters_bound_alt hX h2 hGD hQd hSi hTo hSA hDG hS hF).and (GlobalTheory.T.size_bounds_for_family hS)).and (GlobalTheory.T.weight_parameter_strict_antitone hS)).and hS).and hF).and hDe).and hSh) ?_` and prove the remaining obligations.

Introduce `eps Fm CH _ H`. Take `⟨⟨⟨⟨⟨⟨⟨_, _, hR⟩, _, _, hZ⟩, _, _, hQu⟩, CS, _, hSz⟩, _, _, hFl⟩, _, _, hDg⟩, _, _, hSr⟩` from `H`. Use `⟨10000 + 2 * Cp, by positivity, ?_⟩` and prove the remaining obligations. Take `⟨x0, H⟩` from `((((((hR.and hZ).and hQu).and hSz).and hFl).and hDg).and hSr)`. Use `⟨x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩` and prove the remaining obligations.

Take `⟨⟨⟨⟨⟨⟨hR, hZ⟩, hQu⟩, hSz⟩, hFl⟩, hDg⟩, hSr⟩` from `H x hx hle ι p hp`. Use `set PP := (Fm.parT x hx ι).PP`. Use `set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ with hPdef`. Take `⟨hp1, hq1, hfin, hqe, hanti, ⟨w, hw, huM⟩, -⟩` from `hQu i hi`. Take `rfl` from `hqe u1 hu1`.

Take `⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, hflat, -, hZPP, hTPP, hzb, hz2, -, -⟩` from `hZ i hi Y hY`. Take `⟨hb1, hbU, -, -, -, hbPP, hSq⟩` from `hSz i`. Take `⟨hT, hρ, -, -⟩` from `(hSq hi).2 _ hu1`. Establish `hY1` using `hY.1`. Establish `hAG` using `hgood (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (P.wt (lenT p i PP)) (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P (lenT p i PP) (fun τ => (hanti τ).1) (by omega) hp1 hq1 τ).1) (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (d …`.

Establish `hFZ` using `hFl i hi Y hY`. Establish `hrkZ` using `(hrk (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 _ hFZ).1`. Establish `htwZ` using `htw (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (Fm.L x ι).sc.L hL1 hM hfs hfr (le_of_eq (by rw [zBase])) _ hFZ (by rw [abs_neg]; exact hflat) (P.wt (lenT p i PP)) w`. Establish `hDf : 1 ≤ CompHt.dimFlag (dat p i)`. Rewrite using `[GlobalTheory.CovTop.WtShape.dim_eq]`.

Conclude with `Nat.mul_pos (by omega) (Nat.choose_pos (by omega))`. Establish `hz1 : 1 ≤ zBase (Fm.L x ι)`. Unfold `zBase`. Establish `a : (8 : ℝ) ≤ (Fm.D x ι).R.f` using `by exact_mod_cast hf8`. Establish `b : (100 : ℝ) ≤ (Fm.D x ι).R.r` using `by exact_mod_cast hr100`.

Establish `c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hPP1 : 1 ≤ PP` using `(one_le_pow₀ hz1).trans hZPP`. Establish `hLz : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι)`. Unfold `zBase`.

Establish `a : (8 : ℝ) ≤ (Fm.D x ι).R.f` using `by exact_mod_cast hf8`. Establish `b : (100 : ℝ) ≤ (Fm.D x ι).R.r` using `by exact_mod_cast hr100`. Establish `c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities. Establish `hz12 : zBase (Fm.L x ι) ≤ zBase (Fm.L x ι) ^ 12` using `le_self_pow₀ hz1 (by norm_num)`.

Establish `hlb : Real.log (Fm.L x ι).sc.b ≤ PP`. Rewrite using `[Formalism.BasicNotions.Scale.b, Real.log_exp]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT1 : (1 : ℝ) ≤ (lenT p i PP : ℝ)` using `by exact_mod_cast (by omega : 1 ≤ lenT p i PP)`. Establish `hsq : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b`.

Use `Real.sq_sqrt (show (0 : ℝ) ≤ (Fm.L x ι).sc.b by linarith)` as an intermediate fact. Use `Real.one_le_sqrt.2 hb1` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hZb : zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.b`. Establish `a1 : zBase (Fm.L x ι) ^ 2 ≤ zBase (Fm.L x ι) ^ 12` using `pow_le_pow_right₀ hz1 (by norm_num)`.

Establish `a2 : PP ≤ (lenT p i PP : ℝ) * PP` using `le_mul_of_one_le_left (by linarith) hT1`. Conclude with `a1.trans (hZPP.trans (a2.trans (hTPP.trans hsq)))`. Establish `hkap : 0 ≤ kap p i` using `le_of_lt (pos_of_mul_pos_right (by linarith) (by linarith : (0 : ℝ) ≤ PP))`. Establish `hz0 : 0 ≤ zed p i PP P.u₁`. Unfold `zed`.

Conclude with `mul_nonneg (by norm_num) (add_nonneg (by positivity) (mul_nonneg (by positivity) hρ))`. Establish `hDf0 : (0 : ℝ) < CompHt.dimFlag (dat p i)` using `by exact_mod_cast hDf`. Use `⟨26 * (26 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 + 2 * zed p i PP P.u₁ * lenT p i PP), 4000 * (Fm.L x ι).sc.b + 2 * (Cp * zBase (Fm.L x ι) ^ 2), by positivity, by positivity, ?_, fun Z => ?_⟩` and prove the remaining obligations. Establish `hA` using `GlobalTheory.hilbertSamuel_ALogA_le (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (Fm.L x ι).sc.b (zed p i PP P.u₁) hDf (by omega) hPP1 hb1 hlb hTPP hz0 hz2`. Establish `e1` using `mul_le_mul_of_nonneg_left hZb hCp`.

Establish `e2` using `mul_le_mul_of_nonneg_left hbU (by positivity : (0 : ℝ) ≤ 10000 + 2 * Cp)`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨n, Λ, β, ΛD, ΛT, J, hn, hΛ, hβ, hΛD, hΛT, hln, hlβ, hlδ, hlΛ, hlΛD, hlΛT, hJ, hcl⟩` from `hR i hi Y hY Z`. Take `⟨δ0, hδ0, hδ⟩` from `hDg i hi Y hY _ hu1`. Establish `hdg : 1 ≤ Y.dg P.u₁ Z`.

Establish `h0 : (0 : ℝ) < Y.dg P.u₁ Z` using `hδ0.trans_le (hδ Z).1`. Simplify using `only [Deep.dg] at h0 ⊢`. Conclude with `Nat.one_le_cast.2 (Nat.cast_pos.1 h0)`. Establish `hsh` using `hSr i hi Y hY _ hu1 Z`. Rewrite `hsh` using `[huM, hrkZ]`.

Establish `hbin : (1 : ℝ) ≤ binT p i PP`. Unfold `binT`. Conclude with `Nat.one_le_cast.2 (Nat.choose_pos (by omega))`. Establish `hd : 0 < Y.rkC (P.wt (lenT p i PP)) Z` using `by nlinarith [hsh.1]`. Establish `htwz` using `htwZ Z hw (hAG.2 Z)`.

Rewrite `htwz` using `[← huM]`. Conclude with `GlobalTheory.CovHSNum.deg_bound_of_claim_numbers (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (kap p i) (Fm.L x ι).sc.b (zed p i PP P.u₁) (CompHt.rhoB (dat p i) P.u₁) n Λ β ΛD ΛT J (Y.dg P.u₁ Z) (Y.ht P.u₁ Z) (Y.rkC (P.wt (lenT p i PP)) Z) (Y.degC (P.wt (lenT p i PP)) Z) (Y.degC ( …`.
-/
theorem hilbertSamuel_of_component_estimates : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted →
    GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg →
    Share → HS := by
  intro hX h2 hGD hQd hSi hTo hSA hDG hS hF hDe hSh
  obtain ⟨Cp, hCp, htw⟩ := _root_.GlobalTheory.T.twisted_bundle_degree_lower_bound h2
  have hrk := _root_.GlobalTheory.T.twisted_flat_bundle_ranks h2
  have hgood := _root_.GlobalTheory.T.covering_domain_lattice_regularity h2
  refine Closed.imp (((((((_root_.GlobalTheory.T.exists_degree_parameters_bound_alt hX h2 hGD hQd hSi hTo hSA hDG hS hF).and (GlobalTheory.T.size_bounds_for_family hS)).and (GlobalTheory.T.weight_parameter_strict_antitone hS)).and hS).and hF).and
    hDe).and hSh) ?_
  intro eps Fm CH _ H
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _, hR⟩, _, _, hZ⟩, _, _, hQu⟩, CS, _, hSz⟩, _, _, hFl⟩, _, _, hDg⟩, _, _, hSr⟩ := H
  refine ⟨10000 + 2 * Cp, by positivity, ?_⟩
  obtain ⟨x0, H⟩ := ((((((hR.and hZ).and hQu).and hSz).and hFl).and hDg).and hSr)
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY u1 hu1 => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨hR, hZ⟩, hQu⟩, hSz⟩, hFl⟩, hDg⟩, hSr⟩ := H x hx hle ι p hp
  set PP := (Fm.parT x hx ι).PP
  set P : WtPar (dat p i) := ⟨uW p i, cZero (Fm.D x ι) ((i : ℕ) + 1), (Fm.D x ι).R.k - 2, lenT p i PP⟩ with hPdef
  obtain ⟨hp1, hq1, hfin, hqe, hanti, ⟨w, hw, huM⟩, -⟩ := hQu i hi
  obtain rfl := hqe u1 hu1
  obtain ⟨hLaws, hInR, hL1, hM, hfs, hfr, -, -, hf8, hr100, hflat, -, hZPP, hTPP, hzb, hz2, -, -⟩ := hZ i hi Y hY
  obtain ⟨hb1, hbU, -, -, -, hbPP, hSq⟩ := hSz i
  obtain ⟨hT, hρ, -, -⟩ := (hSq hi).2 _ hu1
  have hY1 := hY.1
  have hAG := hgood (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (P.wt (lenT p i PP))
    (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P (lenT p i PP) (fun τ => (hanti τ).1) (by omega) hp1 hq1 τ).1)
    (fun τ => (GlobalTheory.CompHS.WtPar.antitone_wt_gap_bar (dat p i) P (lenT p i PP) (fun τ => (hanti τ).1) (by omega) hp1 hq1 τ).2)
  have hFZ := hFl i hi Y hY
  have hrkZ := (hrk (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 _ hFZ).1
  have htwZ := htw (Fm.D x ι) p.T hLaws ((i : ℕ) + 1) hp1 hq1 hfin hInR Y _ _ hY1 (Fm.L x ι).sc.L hL1 hM hfs hfr (le_of_eq (by rw [zBase]))
    _ hFZ (by rw [abs_neg]; exact hflat) (P.wt (lenT p i PP)) w
  have hDf : 1 ≤ CompHt.dimFlag (dat p i) := by
    rw [GlobalTheory.CovTop.WtShape.dim_eq]
    exact Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  have hz1 : 1 ≤ zBase (Fm.L x ι) := by
    unfold zBase
    have a : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have b : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hPP1 : 1 ≤ PP := (one_le_pow₀ hz1).trans hZPP
  have hLz : (Fm.L x ι).sc.L ≤ zBase (Fm.L x ι) := by
    unfold zBase
    have a : (8 : ℝ) ≤ (Fm.D x ι).R.f := by exact_mod_cast hf8
    have b : (100 : ℝ) ≤ (Fm.D x ι).R.r := by exact_mod_cast hr100
    have c : (1 : ℝ) ≤ (Fm.D x ι).R.f * (Fm.D x ι).R.r := by nlinarith
    nlinarith
  have hz12 : zBase (Fm.L x ι) ≤ zBase (Fm.L x ι) ^ 12 := le_self_pow₀ hz1 (by norm_num)
  have hlb : Real.log (Fm.L x ι).sc.b ≤ PP := by
    rw [Formalism.BasicNotions.Scale.b, Real.log_exp]
    linarith
  have hT1 : (1 : ℝ) ≤ (lenT p i PP : ℝ) := by exact_mod_cast (by omega : 1 ≤ lenT p i PP)
  have hsq : Real.sqrt (Fm.L x ι).sc.b ≤ (Fm.L x ι).sc.b := by
    have := Real.sq_sqrt (show (0 : ℝ) ≤ (Fm.L x ι).sc.b by linarith)
    have := Real.one_le_sqrt.2 hb1
    nlinarith
  have hZb : zBase (Fm.L x ι) ^ 2 ≤ (Fm.L x ι).sc.b := by
    have a1 : zBase (Fm.L x ι) ^ 2 ≤ zBase (Fm.L x ι) ^ 12 := pow_le_pow_right₀ hz1 (by norm_num)
    have a2 : PP ≤ (lenT p i PP : ℝ) * PP := le_mul_of_one_le_left (by linarith) hT1
    exact a1.trans (hZPP.trans (a2.trans (hTPP.trans hsq)))
  have hkap : 0 ≤ kap p i := le_of_lt (pos_of_mul_pos_right (by linarith) (by linarith : (0 : ℝ) ≤ PP))
  have hz0 : 0 ≤ zed p i PP P.u₁ := by
    unfold zed
    exact mul_nonneg (by norm_num) (add_nonneg (by positivity) (mul_nonneg (by positivity) hρ))
  have hDf0 : (0 : ℝ) < CompHt.dimFlag (dat p i) := by exact_mod_cast hDf
  refine ⟨26 * (26 * (CompHt.dimFlag (dat p i) : ℝ) ^ 2 + 2 * zed p i PP P.u₁ * lenT p i PP),
    4000 * (Fm.L x ι).sc.b + 2 * (Cp * zBase (Fm.L x ι) ^ 2), by positivity, by positivity, ?_, fun Z => ?_⟩
  · have hA := GlobalTheory.hilbertSamuel_ALogA_le (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (Fm.L x ι).sc.b (zed p i PP P.u₁) hDf (by omega)
      hPP1 hb1 hlb hTPP hz0 hz2
    have e1 := mul_le_mul_of_nonneg_left hZb hCp
    have e2 := mul_le_mul_of_nonneg_left hbU (by positivity : (0 : ℝ) ≤ 10000 + 2 * Cp)
    nlinarith
  obtain ⟨n, Λ, β, ΛD, ΛT, J, hn, hΛ, hβ, hΛD, hΛT, hln, hlβ, hlδ, hlΛ, hlΛD, hlΛT, hJ, hcl⟩ := hR i hi Y hY Z
  obtain ⟨δ0, hδ0, hδ⟩ := hDg i hi Y hY _ hu1
  have hdg : 1 ≤ Y.dg P.u₁ Z := by
    have h0 : (0 : ℝ) < Y.dg P.u₁ Z := hδ0.trans_le (hδ Z).1
    simp only [Deep.dg] at h0 ⊢
    exact Nat.one_le_cast.2 (Nat.cast_pos.1 h0)
  have hsh := hSr i hi Y hY _ hu1 Z
  rw [huM, hrkZ] at hsh
  have hbin : (1 : ℝ) ≤ binT p i PP := by
    unfold binT
    exact Nat.one_le_cast.2 (Nat.choose_pos (by omega))
  have hd : 0 < Y.rkC (P.wt (lenT p i PP)) Z := by nlinarith [hsh.1]
  have htwz := htwZ Z hw (hAG.2 Z)
  rw [← huM] at htwz
  exact GlobalTheory.CovHSNum.deg_bound_of_claim_numbers (lenT p i PP) (CompHt.dimFlag (dat p i)) PP (kap p i) (Fm.L x ι).sc.b (zed p i PP P.u₁)
    (CompHt.rhoB (dat p i) P.u₁) n Λ β ΛD ΛT J (Y.dg P.u₁ Z) (Y.ht P.u₁ Z) (Y.rkC (P.wt (lenT p i PP)) Z)
    (Y.degC (P.wt (lenT p i PP)) Z) (Y.degC (uM p i) Z) (Cp * zBase (Fm.L x ι) ^ 2) hDf hT hPP1 hb1 hlb hTPP rfl hρ hz2 hzb
    hkap hn hΛ hβ hΛD hΛT hdg hd hln hlβ hlδ hlΛ hlΛD hlΛT hJ hsh.2 hcl (by positivity) (by rw [zBase]; exact htwz)
end GlobalTheory.CovTop.ShortRoad
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates | exact _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates | (intros; apply _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.hilbertSamuel_lower_bound_of_components : GlobalTheory.CovTop.HypothesesX → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalForFanKS → GlobalTheory.Published.SemiAbelianLieSeminegative → DeepGood → Size → FlatDeg → Deg → Share → HS := by
  first | exact @_root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates | exact _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates | (intros; apply _root_.GlobalTheory.CovTop.ShortRoad.hilbertSamuel_of_component_estimates <;> assumption)
end
