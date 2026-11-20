import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.AgreementPos
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import GroundTheory.HeightsAndTheta.Heights.Regularisation.BoundedStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeLatticeFlagBound
import Development.AutomorphicSpectrum.Statements.GeometryStatements.TrivFlagOnHodge
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.PadicIntegersHenselianFiniteResidue
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerRealAgreementStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerProportionalStatement
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.TestPolynomialShiftTotalStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModelsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MeasureLimitStatementHoldsStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularizedHodgeMetricSmooth
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionFormulaOfArithSystem
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StokesLimitIffPosOfResK
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenFibreExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspIntersectionHeight
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginIntersectionRelayStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PtsIntegralFibreAppendEqMulImageStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp

/- English proof (translation)
Introduce `hAg hPr hCmp hGiv hPts E _ _ _ _ H D Xo l c Y _ T o II hGl hEx hII hp hq B B₁ a K _ J _ Ω _ _ W _ _ Dc O Lt _ _ _ X Or hB hBB hqp hbg hsm hGood hgen hS`. Establish `hIn : PB.Inputs` using `hGiv.2.2.2.2.2.2.2.2.2.1`. Use `haveI : Nonempty (CMType H) := GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.cm_nonempty H`. Establish `hUnif` using `GlobalTheory.T.good_tower_real_agreement hGiv E H D Xo l c Y T o II hGl hEx hII hp hq`. Establish `hProp : T.Proportional` using `GlobalTheory.T.real_tower_proportional hPr hIn II hII (CMType H) (D.p + D.q) T (Top.realOf o.toTowerOrigin) hUnif`.

Establish `hJpos : 0 < Top.testDeg (CMType H) (D.p + D.q) T.j` using `(GlobalTheory.T.test_polynomial_shift_total (CMType H) (D.p + D.q) T.j T.j_pos T.j_lt).2.1`. Establish `hLim : ArLimExists X.H X.S B` using `(GlobalTheory.T.height_comparison_between_models hGiv hPts K J II (CMType H) Ω W Dc X.H X.M X.M X.S X.S B hII X.S_tied X.S_tied).1`. Establish `hMass` using `(GlobalTheory.T.measure_limit_statement_holds II (CMType H) K J Ω W Dc O Lt X B hII.1 hLim).2`. Establish `hSm` using `GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log K J II (CMType H) Ω W Dc X.H X.M X.S B X.S_tied`. Take `⟨K₃, _, ι₃, _, κ, v, P₃, e, r, cf, Mt, Nt, δ, hb, hY, himg, hδ, hdeg, hNs, hpull, hT, hGeo⟩` from `GlobalTheory.T.good_origin_intersection_relay hAg hPr hCmp hGiv hPts E H D Xo l c Y T o II hGl hEx hII hp hq B B₁ a K J Ω W Dc O Lt X Or hB hBB hqp hbg hsm hGood hgen hS`.

Establish `hXar : IsArithVar (imageZ v P₃) (Dc.n + 1)` using `by rw [himg]; exact Dc.arith`. Take `⟨G⟩` from `GlobalTheory.CompanionTheory.Ar.PB.Known.genFibreExists K J K₃ ι₃ κ v P₃ _ hb hY`. Take `⟨Jf, hJf, -⟩` from `(GlobalTheory.CompanionTheory.Ar.PB.Known.fieldNumbers G.Φ (FibreBlock κ) (fibreIdx ι₃ κ)).1`. Establish `hPF` using `GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula ⟨II, hII⟩`. Use `set fibN : Fin r → ℝ := fun m => (Jf (fibreIdeal κ G) e (fun i => fibreDeg κ (Nt 1 m i).a) : ℝ) with hfibN`.

Use `set fib : ℝ := ∑ m, cf m * fibN m with hfib`. Establish `hEq1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m)) = fib * arLimFun X.H X.S B t` using `by filter_upwards [hSm, hpull] with t ht hp'`. Rewrite using `[hfib, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `h` using `hPF II hII.1 K J K₃ ι₃ κ v P₃ (Dc.n + 1) e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt t m) hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs t m)`.

Establish `hd : (fun i => fibreDeg κ (Nt t m i).a) = fun i => fibreDeg κ (Nt 1 m i).a`. Use function extensionality and compare the values at `i`. Rewrite using `[hdeg t m i]`. Rewrite using `[h, himg, hd]`. Simplify using `only [arLimFun, hfibN]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hEq2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) = fib * geomDeg (mCoordIdeal Dc.y) (muReg X.H X.S B t) Dc.n` using `by filter_upwards [hSm, hpull, hGeo] with t ht hp' hg`. Rewrite using `[← hg, hfib, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image II hII K J K₃ ι₃ κ v P₃ Dc.n e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt 1 m) hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs 1 m)`.

Rewrite using `[h, himg]`. Simplify using `only [geomDeg, hfibN]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨L, hL⟩` from `hLim`. Establish `hA : arLim X.H X.S B = L` using `hL.limUnder_eq`.

Establish `h1 : δ * T.PPc II B a (Top.testPoly T.j) = fib * L` using `tendsto_nhds_unique hT ((hL.const_mul fib).congr' (hEq1.mono fun t h => h.symm))`. Establish `h2 : δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) = fib * degMu X.H` using `tendsto_nhds_unique (tendsto_const_nhds.congr' hEq2) (hMass.const_mul fib)`. Establish `h3 : (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) = T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j` using `hProp.2.1 B a _`. Rewrite `h2` using `[h3]`. Establish `hvol : 0 < T.vol a` using `hProp.1 a`.

Establish `hvJ : 0 < T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j` using `mul_pos hvol hJpos`. Establish `hpos : 0 < fib * degMu X.H` using `by rw [← h2]; exact mul_pos hδ hvJ`. Establish `hd0 : 0 ≤ degMu X.H` using `GlobalTheory.CompanionTheory.StokesCompare.degMu_nonneg X`. Establish `hdpos : 0 < degMu X.H`. Use `lt_of_le_of_ne hd0 fun h => ?_` and prove the remaining obligations.

Rewrite `hpos` using `[← h, mul_zero]`. Conclude with `lt_irrefl _ hpos`. Use `⟨hdpos, ⟨L, hL⟩, ?_⟩` and prove the remaining obligations. Establish `hj : Dc.j = D.p`. Break down `Or.side with ⟨-, -, h⟩ | ⟨h, -, -⟩` into its components or cases.

Conclude with `h`. Take `⟨τ⟩` from `(inferInstance : Nonempty (CMType H))`. Use `congrFun (hbg.symm.trans h) τ` as an intermediate fact. Simplify using `at this`. Establish `hNn : Dc.N = D.p + D.q` using `Or.N_eq`.

Establish `hdim : ((Dc.n + 1 : ℕ) : ℝ) = (Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1`. Establish `hjT : T.j = D.p` using `o.j_eq`. Establish `: Dc.n = Top.dimX (CMType H) (D.p + D.q) T.j`. Simplify using `only [ComponentData.n, Top.dimX, hj, hNn, hjT]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hne : ((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) ≠ 0` using `by positivity`. Establish `hsl : slX X B = L / (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * degMu X.H)`.

Rewrite using `[slX, hA, hdim]`. Rewrite using `[hsl]`. Apply `mul_left_cancel₀ hδ.ne'` to reduce the goal to its premises. Rewrite using `[h1]`. Establish `hdn` using `hdpos.ne'`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `(-L) * h2`.
-/
theorem testPoly_eq_slX : PB.AgreementPos → PB.Proportional → Cmp.CmpSt → Top.Given → PtsIntegrableStatement → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : Top.RootTower (CMType H) (D.p + D.q)) (o : Top.GoodOrigin Y T) (II : IntersectionSystem), Top.IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∀ (B B₁ : ℕ) (a : T.Comp) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (O Lt : Type) [CommRing O] [AddCommGroup Lt] [Module O Lt] (X : ComponentSetting Dc O Lt) (Or : CptOrigin Y T.bad Dc X.H), 2 ≤ B → B ≤ B₁ → D.q ≤ D.p → Or.bg = Sum.inl → Or.sm = Sum.inr → Or.Good → genPt Or.𝔐.ξ₀ = genPt (o.Fx a).ξf → (∀ r : ℕ, r ∈ Dc.S ↔ r.Prime ∧ r ≤ B₁ ∧ r ∉ T.bad) → 0 < degMu X.H ∧ ArLimExists X.H X.S B ∧ T.PPc II B a (Top.testPoly T.j) = slX X B * (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * (T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j)) := by
  intro hAg hPr hCmp hGiv hPts E _ _ _ _ H D Xo l c Y _ T o II hGl hEx hII hp hq B B₁ a K _ J _ Ω _ _ W _ _ Dc O Lt _ _ _ X Or hB hBB hqp hbg hsm hGood hgen hS
  have hIn : PB.Inputs := hGiv.2.2.2.2.2.2.2.2.2.1
  haveI : Nonempty (CMType H) := GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.cm_nonempty H
  have hUnif := GlobalTheory.T.good_tower_real_agreement hGiv E H D Xo l c Y T o II hGl hEx hII hp hq
  have hProp : T.Proportional :=
    GlobalTheory.T.real_tower_proportional hPr hIn II hII (CMType H) (D.p + D.q) T (Top.realOf o.toTowerOrigin) hUnif
  have hJpos : 0 < Top.testDeg (CMType H) (D.p + D.q) T.j :=
    (GlobalTheory.T.test_polynomial_shift_total (CMType H) (D.p + D.q) T.j T.j_pos T.j_lt).2.1
  have hLim : ArLimExists X.H X.S B :=
    (GlobalTheory.T.height_comparison_between_models hGiv hPts K J II (CMType H) Ω W Dc X.H X.M X.M X.S X.S B hII X.S_tied X.S_tied).1
  have hMass := (GlobalTheory.T.measure_limit_statement_holds II (CMType H) K J Ω W Dc O Lt X B hII.1 hLim).2
  have hSm := GlobalTheory.CompanionTheory.Ar.Cusp.muReg_smooth_log K J II (CMType H) Ω W Dc X.H X.M X.S B X.S_tied
  obtain ⟨K₃, _, ι₃, _, κ, v, P₃, e, r, cf, Mt, Nt, δ, hb, hY, himg, hδ, hdeg, hNs, hpull, hT, hGeo⟩ :=
    GlobalTheory.T.good_origin_intersection_relay hAg hPr hCmp hGiv hPts E H D Xo l c Y T o II hGl hEx hII hp hq B B₁ a K J Ω W Dc O Lt X Or hB hBB hqp hbg hsm hGood hgen hS
  have hXar : IsArithVar (imageZ v P₃) (Dc.n + 1) := by rw [himg]; exact Dc.arith
  obtain ⟨G⟩ := GlobalTheory.CompanionTheory.Ar.PB.Known.genFibreExists K J K₃ ι₃ κ v P₃ _ hb hY
  obtain ⟨Jf, hJf, -⟩ := (GlobalTheory.CompanionTheory.Ar.PB.Known.fieldNumbers G.Φ (FibreBlock κ) (fibreIdx ι₃ κ)).1
  have hPF := GlobalTheory.CompanionTheory.Ar.Giv.ProjF.projFormula ⟨II, hII⟩
  set fibN : Fin r → ℝ := fun m => (Jf (fibreIdeal κ G) e (fun i => fibreDeg κ (Nt 1 m i).a) : ℝ) with hfibN
  set fib : ℝ := ∑ m, cf m * fibN m with hfib
  have hEq1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∑ m, cf m * II K₃ ι₃ P₃ (Dc.n + 1 + e) (Fin.append (fun _ : Fin (Dc.n + 1) => Mt t) (Nt t m)) =
      fib * arLimFun X.H X.S B t := by
    filter_upwards [hSm, hpull] with t ht hp'
    rw [hfib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h := hPF II hII.1 K J K₃ ι₃ κ v P₃ (Dc.n + 1) e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt t m)
      hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs t m)
    have hd : (fun i => fibreDeg κ (Nt t m i).a) = fun i => fibreDeg κ (Nt 1 m i).a := by
      funext i; rw [hdeg t m i]
    rw [h, himg, hd]
    simp only [arLimFun, hfibN]
    ring
  have hEq2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) =
      fib * geomDeg (mCoordIdeal Dc.y) (muReg X.H X.S B t) Dc.n := by
    filter_upwards [hSm, hpull, hGeo] with t ht hp' hg
    rw [← hg, hfib, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    have h := GlobalTheory.T.ptsIntegral_fibre_append_eq_mul_image II hII K J K₃ ι₃ κ v P₃ Dc.n e G Jf (fun _ => muReg X.H X.S B t) (fun _ => Mt t) (Nt 1 m)
      hb hY hXar hJf (fun _ => ht.1) (fun _ => hp') (hNs 1 m)
    rw [h, himg]
    simp only [geomDeg, hfibN]
    ring
  obtain ⟨L, hL⟩ := hLim
  have hA : arLim X.H X.S B = L := hL.limUnder_eq
  have h1 : δ * T.PPc II B a (Top.testPoly T.j) = fib * L :=
    tendsto_nhds_unique hT ((hL.const_mul fib).congr' (hEq1.mono fun t h => h.symm))
  have h2 : δ * (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) = fib * degMu X.H :=
    tendsto_nhds_unique (tendsto_const_nhds.congr' hEq2) (hMass.const_mul fib)
  have h3 : (T.M B a).geoFun (Top.toA (Top.muSmall T.j ^ Top.dimX (CMType H) (D.p + D.q) T.j * Top.fibClass T.j : Top.RP (CMType H) (D.p + D.q))) =
      T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j := hProp.2.1 B a _
  rw [h3] at h2
  have hvol : 0 < T.vol a := hProp.1 a
  have hvJ : 0 < T.vol a * Top.testDeg (CMType H) (D.p + D.q) T.j := mul_pos hvol hJpos
  have hpos : 0 < fib * degMu X.H := by rw [← h2]; exact mul_pos hδ hvJ
  have hd0 : 0 ≤ degMu X.H := GlobalTheory.CompanionTheory.StokesCompare.degMu_nonneg X
  have hdpos : 0 < degMu X.H := by
    refine lt_of_le_of_ne hd0 fun h => ?_
    rw [← h, mul_zero] at hpos
    exact lt_irrefl _ hpos
  refine ⟨hdpos, ⟨L, hL⟩, ?_⟩
  have hj : Dc.j = D.p := by
    rcases Or.side with ⟨-, -, h⟩ | ⟨h, -, -⟩
    · exact h
    · obtain ⟨τ⟩ := (inferInstance : Nonempty (CMType H))
      have := congrFun (hbg.symm.trans h) τ
      simp at this
  have hNn : Dc.N = D.p + D.q := Or.N_eq
  have hdim : ((Dc.n + 1 : ℕ) : ℝ) = (Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1 := by
    have hjT : T.j = D.p := o.j_eq
    have : Dc.n = Top.dimX (CMType H) (D.p + D.q) T.j := by
      simp only [ComponentData.n, Top.dimX, hj, hNn, hjT]
      ring
    rw [this]
    push_cast
    ring
  have hne : ((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) ≠ 0 := by positivity
  have hsl : slX X B = L / (((Top.dimX (CMType H) (D.p + D.q) T.j : ℝ) + 1) * degMu X.H) := by
    rw [slX, hA, hdim]
  rw [hsl]
  apply mul_left_cancel₀ hδ.ne'
  rw [h1]
  have hdn := hdpos.ne'
  field_simp
  linear_combination (-L) * h2

end GlobalTheory.CompanionTheory.Ar.Cusp
