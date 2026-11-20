import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelThetaSpan
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsVacuaAndMultipliers
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAdelicMatrix
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelDatumVectorEqThetaOfTestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsTrivialAtLevelUnitaryTransportSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevelStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorTestThetaZeroEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinearStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AdelicZakThetaExistsUniqueStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.FockPolynomialVectorLawsStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReadOffFormsAutomorphicInverseMultiplierStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormsOfBoundedAdelicFunctionNormBoundedStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesEvalLevelTrivialMulRealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelGroupCongruentOfTwoLatticeMovesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfRationalLevelInvariantAgreeChosenStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSeriesFockVectorInvarianceStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D S T C om hW hsz Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hhol hγ hk hbdd`. Take `⟨v₀, μ, hv, hμ⟩` from `GlobalTheory.SW.exists_vacua_and_multipliers D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv`. Take `⟨ep, cf, hep⟩` from `GlobalTheory.T.weilPair_levelTrivial_maps_levelVector D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB`. Establish `hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ` using `by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _`. Establish `hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank)`.

Rewrite using `[GlobalTheory.Ker.Red.fmtC_one]`. Conclude with `GlobalTheory.Ker.Red.isMov_one _`. Take `⟨hV, hL⟩` from `GlobalTheory.T.self_dual_lattices_at_level D S T C`. Establish `hΛl : C.X.Λ ∈ Lv.lats` using `(hL Lv 1 _ C.X.Λ_fg hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)`. Take `⟨t, ht0, hft⟩` from `(GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase (v₀ C.X.Λ) (hv _ hΛl)`.

Establish `hu : C.uVec Lv hn f' = t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))`. Rewrite using `[hft]`. Conclude with `((GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv).2 t`. Establish `hex : ∀ L : Lt D.host.E T.rank, ∃ g : GA D T, L ∈ Lv.lats → g ∈ GfC T ∧ TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L`. Introduce `L`.

Distinguish the cases in `hL' : L ∈ Lv.lats`. Take `⟨g, hg, h1, h2⟩` from `GlobalTheory.Ker.OntoLat.exists_trivAt_mov D S T C Lv L hL'`. Conclude with `⟨g, fun _ => ⟨hg, h1, h2⟩⟩`. Conclude with `⟨1, fun h => absurd h hL'⟩`. Use `choose gL hgL using hex`.

Use `choose Qf hQd hQb hQv using fun L => hhol (gL L)`. Establish `hne : ∀ L ∈ Lv.lats, ep 1 * cf (gL L) ≠ 0`. Introduce `L hL'`. Take `⟨g1, g2, -⟩` from `hep 1 _ (gL L) L (one_mem _) (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1 (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2`. Apply the tactic sequence `refine mul_ne_zero ?_ ?_ <;> intro h0`.

Rewrite `g1` using `[h0, norm_zero]`. Conclude with `zero_ne_one g1`. Rewrite `g2` using `[h0, norm_zero]`. Conclude with `zero_ne_one g2`. Set `F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ` to `fun L x => Qf L x / (ep 1 * cf (gL L))`.

Establish `hFhol : ∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom` using `fun L _ => by show DifferentiableOn ℂ (fun x => Qf L x / (ep 1 * cf (gL L))) C.X.dom`. Simplify `(hQd L).mul_const (ep 1 * cf (gL L))⁻¹` using `only [div_eq_mul_inv]`. Establish `hFbor : ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x`. Introduce `L _ x hx b hb`. Use `show Qf L (rmul x b) / _ = _ * (Qf L x / _)`.

Rewrite using `[hQb L x hx b hb, mul_div_assoc]`. Establish `hFv : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))`. Introduce `L hL' a ha`. Use `show _ = _ * (Qf L _ / _)`. Rewrite using `[hQv L a ha, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (hne L hL')]`.

Establish `hForm : IsForm C.X Lv.grp Lv.lats μ (wtOf C.X C.hr c c' S.rank) F` using `⟨hFhol, hFbor, GlobalTheory.T.readOffForms_automorphic_inverse_multiplier D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep gL hgL F hFhol hFbor hFv, GlobalTheory.T.forms_of_bounded_adelic_function_norm_bounded D S T C om hW Lv hn M hw hM hM𝔪 B …`. Take `⟨m, Λs, P, a, hΛP, hsp⟩` from `GlobalTheory.SW.level_theta_span D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx S.rank C.sympl C.even hsz Lv hn M hM hM𝔪 v₀ hv μ hμ c c' F hForm`. Use `choose hs hsf hst hsm using fun i => GlobalTheory.T.exists_trivialAtLevel_unitary_transport_selfDual D S T C M hM (Λs i) (hΛP i).1`. Establish `hbij` using `(GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).1`. Set `Qs : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ` to `fun i => Function.surjInv hbij.2 (P i)`.

Establish `hQs : ∀ i, C.toH (Qs i) = P i` using `fun i => Function.surjInv_eq hbij.2 (P i)`. Establish `hepn : ∀ i, ep (hs i) ≠ 0`. Introduce `i h0`. Take `⟨g1, -⟩` from `hep (hs i) (Λs i) 1 C.X.Λ (hsf i) (hst i) (hΛP i).1.1 (hsm i) (one_mem _) (GlobalTheory.Ker.Red.trivAt_one _ _) C.X.Λ_fg hm1`. Rewrite `g1` using `[h0, norm_zero]`.

Conclude with `zero_ne_one g1`. Set `Θ : Fin m → GA D T → ℂ` to `fun i g => om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0`. Set `ψ : GA D T → ℂ` to `∑ i, (a i * ep 1 / (t * ep (hs i))) • Θ i`. Establish `hψ : ∀ g, ψ g = ∑ i, (a i * ep 1 / (t * ep (hs i))) * Θ i g`. Introduce `g`.

Simplify using `only [ψ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Establish `hψmem : ψ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c')` using `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨hs i, Qs i, by rw [hQs i]; exact (hΛP i).2, rfl⟩)`. It suffices to establish `hφψ : φ = ψ by rw [hφψ]; exact hψmem`. Use `set u0 := C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) with hu0`. Establish `hJ` using `(GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2`.

Establish `hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M` using `hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1`. Establish `hth0 : C.IsTh u0` using `(GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B hB).2.1 _ (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv C.X.Λ hΛl _ hstd).1).1.1`. Establish `hΘ : ∀ i g, Θ i g = t * om (hs i, g) (C.fvec B u0 (Qs i)) 0`. Introduce `i g`. Use `show om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0 = _`.

Rewrite using `[hu, (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) u0 hth0 (Qs i)).2.2.2.2.1 t, map_smul, Pi.smul_apply, smul_eq_mul]`. Establish `hk0 : ∀ k, C.LevK Lv k 1 → om (1, k) u0 = u0`. Introduce `k hk'`. Establish `e` using `(hk k 1 hk').1`. Rewrite `e` using `[hu, map_smul]`.

Conclude with `smul_right_injective _ ht0 e`. Establish `hinv` using `fun i => GlobalTheory.T.theta_series_fock_vector_invariance D S T C om hW Lv (hs i) B hB u0 hth0 (Qs i)`. Establish `hψγ : ∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g`. Introduce `γ hγ' g`. Rewrite using `[hψ, hψ]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hΘ, hΘ, (hinv i).1 γ hγ' g]`. Establish `hψk : ∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g`. Introduce `k hk' g`. Rewrite using `[hψ, hψ]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hΘ, hΘ, (hinv i).2 hk0 k hk' g]`. Establish `hag : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a)`. Introduce `L hL' a ha`. Establish `hx : C.xB (C.mvB a B) ∈ C.X.dom` using `(hJ _ ((hJ B hB).2.2.2.2.2 a).1).2.1`.

Establish `hev : ∀ i, Θ i (gL L * a) = t * ep (hs i) * cf (gL L) * z a * thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L (Λs i)) (P i) (C.xB (C.mvB a B))`. Introduce `i`. Use `show om _ (C.fvec B (C.uVec Lv hn f') _) 0 = _`. Rewrite using `[hu, GlobalTheory.T.thetaSeries_eval_levelTrivial_mul_real D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t (hs i) (Λs i) (hsf i) (hst i) (hΛP i).1.1 (hsm i) (gL L) L (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2 a ha (Qs i), hQs i]`. Rewrite using `[hFv L hL' a ha, hψ, hsp L hL' _ hx, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hev i]`. Establish `h1` using `hepn i`. Clear the denominators using the available nonvanishing facts. Conclude with `GlobalTheory.T.eq_of_rational_level_invariant_agree_chosen D S T C Lv M hM hM𝔪 gL hgL φ ψ hγ hψγ (fun k hk' => (hk k 1 hk').2) hψk hag`.
-/
theorem GlobalTheory.AdSpan.mem_span_thetaSet_of_holUpTo : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → 4 * (Module.finrank ℚ D.host.E * T.rank) + 4 ≤ S.rank → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → HolUpTo C B (ThFr.wtOf C.X C.hr c c' S.rank) z φ → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → (∃ K : ℝ, ∀ g, ‖φ g‖ ≤ K) → φ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') := by
  intro D S T C om hW hsz Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hhol hγ hk hbdd
  obtain ⟨v₀, μ, hv, hμ⟩ := GlobalTheory.SW.exists_vacua_and_multipliers D.host.E T.rank C.X C.g C.bas C.idx S.rank
    C.sympl C.even Lv
  obtain ⟨ep, cf, hep⟩ := GlobalTheory.T.weilPair_levelTrivial_maps_levelVector D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB
  have hm1 : IsMov (fmt T 1) C.X.Λ C.X.Λ := by rw [GlobalTheory.Ker.Red.fmt_one]; exact GlobalTheory.Ker.Red.isMov_one _
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [GlobalTheory.Ker.Red.fmtC_one]; exact GlobalTheory.Ker.Red.isMov_one _
  obtain ⟨hV, hL⟩ := GlobalTheory.T.self_dual_lattices_at_level D S T C
  have hΛl : C.X.Λ ∈ Lv.lats := (hL Lv 1 _ C.X.Λ_fg hm1).2.1 (GlobalTheory.Ker.Red.trivAt_one _ _)
  obtain ⟨t, ht0, hft⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase (v₀ C.X.Λ) (hv _ hΛl)
  have hu : C.uVec Lv hn f' = t • C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) := by
    rw [hft]; exact ((GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv).2 t
  have hex : ∀ L : Lt D.host.E T.rank, ∃ g : GA D T, L ∈ Lv.lats →
      g ∈ GfC T ∧ TrivAt T (C.under Lv) g ∧ IsMov (fmt T g) C.X.Λ L := by
    intro L
    by_cases hL' : L ∈ Lv.lats
    · obtain ⟨g, hg, h1, h2⟩ := GlobalTheory.Ker.OntoLat.exists_trivAt_mov D S T C Lv L hL'
      exact ⟨g, fun _ => ⟨hg, h1, h2⟩⟩
    · exact ⟨1, fun h => absurd h hL'⟩
  choose gL hgL using hex
  choose Qf hQd hQb hQv using fun L => hhol (gL L)
  have hne : ∀ L ∈ Lv.lats, ep 1 * cf (gL L) ≠ 0 := by
    intro L hL'
    obtain ⟨g1, g2, -⟩ := hep 1 _ (gL L) L (one_mem _) (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
      (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2
    refine mul_ne_zero ?_ ?_ <;> intro h0
    · rw [h0, norm_zero] at g1; exact zero_ne_one g1
    · rw [h0, norm_zero] at g2; exact zero_ne_one g2
  let F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ := fun L x => Qf L x / (ep 1 * cf (gL L))
  have hFhol : ∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom := fun L _ => by
    show DifferentiableOn ℂ (fun x => Qf L x / (ep 1 * cf (gL L))) C.X.dom
    simpa only [div_eq_mul_inv] using (hQd L).mul_const (ep 1 * cf (gL L))⁻¹
  have hFbor : ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank,
      F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x := by
    intro L _ x hx b hb
    show Qf L (rmul x b) / _ = _ * (Qf L x / _)
    rw [hQb L x hx b hb, mul_div_assoc]
  have hFv : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T,
      φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B)) := by
    intro L hL' a ha
    show _ = _ * (Qf L _ / _)
    rw [hQv L a ha, mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ (hne L hL')]
  have hForm : IsForm C.X Lv.grp Lv.lats μ (wtOf C.X C.hr c c' S.rank) F :=
    ⟨hFhol, hFbor, GlobalTheory.T.readOffForms_automorphic_inverse_multiplier D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv,
     GlobalTheory.T.forms_of_bounded_adelic_function_norm_bounded D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hγ hk v₀ μ hv hμ ep cf hep
      gL hgL F hFhol hFbor hFv hbdd⟩
  obtain ⟨m, Λs, P, a, hΛP, hsp⟩ := GlobalTheory.SW.level_theta_span D.host.E T.rank C.X C.g C.q0 C.hr C.bas C.idx
    S.rank C.sympl C.even hsz Lv hn M hM hM𝔪 v₀ hv μ hμ c c' F hForm
  choose hs hsf hst hsm using fun i => GlobalTheory.T.exists_trivialAtLevel_unitary_transport_selfDual D S T C M hM (Λs i) (hΛP i).1
  have hbij := (GlobalTheory.T.fockPolynomialVector_testTheta_zero_eq_thetaSeries D S T C).1
  let Qs : Fin m → MvPolynomial (FVar D T.rank S.rank) ℂ := fun i => Function.surjInv hbij.2 (P i)
  have hQs : ∀ i, C.toH (Qs i) = P i := fun i => Function.surjInv_eq hbij.2 (P i)
  have hepn : ∀ i, ep (hs i) ≠ 0 := by
    intro i h0
    obtain ⟨g1, -⟩ := hep (hs i) (Λs i) 1 C.X.Λ (hsf i) (hst i) (hΛP i).1.1 (hsm i) (one_mem _)
      (GlobalTheory.Ker.Red.trivAt_one _ _) C.X.Λ_fg hm1
    rw [h0, norm_zero] at g1; exact zero_ne_one g1
  let Θ : Fin m → GA D T → ℂ := fun i g => om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0
  let ψ : GA D T → ℂ := ∑ i, (a i * ep 1 / (t * ep (hs i))) • Θ i
  have hψ : ∀ g, ψ g = ∑ i, (a i * ep 1 / (t * ep (hs i))) * Θ i g := by
    intro g; simp only [ψ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have hψmem : ψ ∈ Submodule.span ℂ (thetaSet C om B (C.uVec Lv hn f') c c') :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨hs i, Qs i, by rw [hQs i]; exact (hΛP i).2, rfl⟩)
  suffices hφψ : φ = ψ by rw [hφψ]; exact hψmem
  set u0 := C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) with hu0
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hstd : stdL D.host.E S.rank ∈ Vset D.host.E S.rank M :=
    hV M 1 _ hM (GlobalTheory.Ker.Red.trivAt_one _ _) (GlobalTheory.Ker.Red.stdL_fg _) hs1
  have hth0 : C.IsTh u0 := (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (hJ B hB).2.1 _
    (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv
      C.X.Λ hΛl _ hstd).1).1.1
  have hΘ : ∀ i g, Θ i g = t * om (hs i, g) (C.fvec B u0 (Qs i)) 0 := by
    intro i g
    show om (hs i, g) (C.fvec B (C.uVec Lv hn f') (Qs i)) 0 = _
    rw [hu, (GlobalTheory.T.fockPolynomialVector_laws D S T C B hB (fun _ => 1) u0 hth0 (Qs i)).2.2.2.2.1 t, map_smul, Pi.smul_apply,
      smul_eq_mul]
  have hk0 : ∀ k, C.LevK Lv k 1 → om (1, k) u0 = u0 := by
    intro k hk'
    have e := (hk k 1 hk').1
    rw [hu, map_smul] at e
    exact smul_right_injective _ ht0 e
  have hinv := fun i => GlobalTheory.T.theta_series_fock_vector_invariance D S T C om hW Lv (hs i) B hB u0 hth0 (Qs i)
  have hψγ : ∀ γ ∈ GQ T, ∀ g, ψ (γ * g) = ψ g := by
    intro γ hγ' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).1 γ hγ' g]
  have hψk : ∀ k, C.LevK Lv k 1 → ∀ g, ψ (g * k) = ψ g := by
    intro k hk' g
    rw [hψ, hψ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΘ, hΘ, (hinv i).2 hk0 k hk' g]
  have hag : ∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = ψ (gL L * a) := by
    intro L hL' a ha
    have hx : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ ((hJ B hB).2.2.2.2.2 a).1).2.1
    have hev : ∀ i, Θ i (gL L * a) = t * ep (hs i) * cf (gL L) * z a *
        thP C.X C.hr C.bas C.idx (Lv.phi C.bas hn v₀ L (Λs i)) (P i) (C.xB (C.mvB a B)) := by
      intro i
      show om _ (C.fvec B (C.uVec Lv hn f') _) 0 = _
      rw [hu, GlobalTheory.T.thetaSeries_eval_levelTrivial_mul_real D S T C om hW Lv hn M hw hM hM𝔪 v₀ hv B hB ep cf hep z hz t (hs i) (Λs i) (hsf i) (hst i)
        (hΛP i).1.1 (hsm i) (gL L) L (hgL L hL').1 (hgL L hL').2.1 hL'.1.1 (hgL L hL').2.2 a ha (Qs i), hQs i]
    rw [hFv L hL' a ha, hψ, hsp L hL' _ hx, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hev i]
    have h1 := hepn i
    field_simp
  exact GlobalTheory.T.eq_of_rational_level_invariant_agree_chosen D S T C Lv M hM hM𝔪 gL hgL φ ψ hγ hψγ (fun k hk' => (hk k 1 hk').2) hψk hag
