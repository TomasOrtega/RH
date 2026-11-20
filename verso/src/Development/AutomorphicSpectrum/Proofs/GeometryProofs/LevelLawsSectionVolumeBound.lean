import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BcMapBcVec
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.FlatChernWeightEqOfIndependence
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.RegularFormsIsBundleProjectiveCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TwistedDualRegularFormsFiniteCover
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.AdelicGLLastRowAndDetModuleUnderLeftMultiplicati
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ThmFlatA
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.LineDegreeClosedFormula
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Statements.GeometryStatements.GoodTwistGoodTwist
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelLawsFrameDictionaryStatement
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec.BergDual

/- English proof (translation)
Break down `hg with rfl | rfl` into its components or cases. Simplify using the standard rewrite rules. Establish `e : (∑ j, ∑ j', starRingEnd ℂ (b j) * starRingEnd ℂ (starRingEnd ℂ (b j')) * starRingEnd ℂ (M j j')) = starRingEnd ℂ (∑ j, ∑ j', b j * starRingEnd ℂ (b j') * M j j')`. Simplify using `only [map_sum, map_mul]`. Rewrite using `[e, Complex.conj_re]`.
-/
theorem re_twist (g : ℂ →+* ℂ) (hg : g = RingHom.id ℂ ∨ g = starRingEnd ℂ) {n : ℕ} (b : Fin n → ℂ)
    (M : Fin n → Fin n → ℂ) :
    (∑ j, ∑ j', g (b j) * starRingEnd ℂ (g (b j')) * g (M j j')).re =
      (∑ j, ∑ j', b j * starRingEnd ℂ (b j') * M j j').re := by
  rcases hg with rfl | rfl
  · simp
  · have e : (∑ j, ∑ j', starRingEnd ℂ (b j) * starRingEnd ℂ (starRingEnd ℂ (b j')) * starRingEnd ℂ (M j j')) =
        starRingEnd ℂ (∑ j, ∑ j', b j * starRingEnd ℂ (b j') * M j j') := by
      simp only [map_sum, map_mul]
    rw [e, Complex.conj_re]

/- English proof (translation)
Rewrite using `[Real.sqrt_le_left (by positivity)]`. Establish `h3 : t * N ≤ (lf * pn * hh) ^ 2 * N`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_of_mul_le_mul_right h3 hN`.
-/
theorem sqrt_le_of_bounds {t N A pn hh lf : ℝ} (hN : 0 < N) (h1 : t * N ≤ (A * pn) ^ 2)
    (h2 : A ^ 2 ≤ lf ^ 2 * N * hh ^ 2) (hlf : 0 < lf) (hpn : 0 < pn) (hh0 : 0 < hh) :
    Real.sqrt t ≤ lf * pn * hh := by
  rw [Real.sqrt_le_left (by positivity)]
  have h3 : t * N ≤ (lf * pn * hh) ^ 2 * N := by
    calc t * N ≤ (A * pn) ^ 2 := h1
      _ = A ^ 2 * pn ^ 2 := by ring
      _ ≤ (lf ^ 2 * N * hh ^ 2) * pn ^ 2 := by gcongr
      _ = (lf * pn * hh) ^ 2 * N := by ring
  exact le_of_mul_le_mul_right h3 hN

/- English proof (translation)
Conclude with `if_pos (goodEmb_goodOf c σ)`.
-/
theorem goodOf_goodOf {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) : goodOf c (goodOf c σ) = goodOf c σ := by
  exact if_pos (goodEmb_goodOf c σ)

/- English proof (translation)
Unfold `Small.goodTwist`. Use `split_ifs`. Conclude with `Or.inl rfl`. Conclude with `Or.inr rfl`.
-/
theorem goodTwist_cases {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : Level H} (c : Coeff l) (σ : c.F →+* ℂ) :
    Small.goodTwist c σ = RingHom.id ℂ ∨ Small.goodTwist c σ = starRingEnd ℂ := by
  unfold Small.goodTwist
  split_ifs
  · exact Or.inl rfl
  · exact Or.inr rfl

end GlobalTheory.CompanionTheory.Ar.Rec.BergDual

open GlobalTheory.CompanionTheory.Ar.Rec.BergDual in

/- English proof (translation)
Introduce `D H Dw l Xo c U h e W dict hL hLev hV a₁ Z n ω I _ L ei hOn hsp σ k y lin hlin hmet hOver hy x0 FF t hO hF ht hB`. Establish `hg` using `goodEmb_goodOf c σ`. Take `⟨P, hP, hN, hPy⟩` from `hB`. Take `⟨-, -, hTie⟩` from `GlobalTheory.T.level_laws_frame_dictionary D H Dw l Xo c U h e W dict hL hLev hV (goodOf c σ) hg Z k hOver a₁ x0 FF hO hF`. Take `⟨m, as, fs, hfs, hPeq⟩` from `hOn (goodOf c σ) hg k hOver P hP`.

Establish `hω : ∀ j, ω j ∈ cuspOn U h a₁ Z` using `fun j => hsp ▸ Submodule.subset_span ⟨j, rfl⟩`. Establish `hb : ∀ i, ∃ b : Fin n → c.F, ∑ j, b j • ω j = fs i` using `fun i => (Submodule.mem_span_range_iff_exists_fun c.F).1 (hsp ▸ hfs i)`. Use `choose b hb using hb`. Take `⟨as', has'⟩ : ∃ as' : Fin n → ℂ, as' = fun j => ∑ i, as i * goodOf c σ (b i j)` from `⟨_, rfl⟩`. Establish `hQ : ∀ x ∈ ((U (goodOf c σ)).X k).dom, P x = ∑ j, as' j * rdU (U (goodOf c σ)) (ω j) k x`.

Introduce `x hx`. Rewrite using `[hPeq x hx]`. Establish `e1 : ∀ i, rdU (U (goodOf c σ)) (fs i) k x = ∑ j, goodOf c σ (b i j) * rdU (U (goodOf c σ)) (ω j) k x`. Introduce `i`. Rewrite using `[← hb i, map_sum]`.

Simplify using `[Finset.sum_apply, map_smulₛₗ]`. Simplify using `only [e1, has', Finset.mul_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `hnrm : ThA.nrm2 ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) P = ThA.nrm2 ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) (fun y => ∑ j, as' j * rdU (U (goodOf c σ)) (ω j) k y)`. Unfold `ThA.nrm2`. Use `congr 1`. Use `setIntegral_congr_fun hF.1 fun z hz => ?_` and prove the remaining obligations. Simplify using `only [Data.pnorm]`.

Rewrite using `[hQ _ (hF.2.1 hz)]`. Establish `hT` using `hTie n as' ω hω`. Rewrite `hT` using `[← hnrm]`. Establish `hm` using `hmet (fun j => Small.goodTwist c σ (as' j))`. Establish `hip : ∀ f g, ipOn U W dict (xiR D) a₁ (e Z) σ f g = Small.goodTwist c σ (ipOn U W dict (xiR D) a₁ (e Z) (goodOf c σ) f g)`.

Introduce `f g`. Unfold `ipOn`. Simplify using `only [goodOf_goodOf, if_pos hg]`. Unfold `Small.goodTwist`. Apply the tactic sequence `split_ifs <;> rfl`.

Establish `hsum : ∑ j, Small.goodTwist c σ (as' j) * lin (ω j) = Small.goodTwist c σ (P y)`. Rewrite using `[hQ y hy, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hlin, map_mul]`. Establish `hre : (∑ j, ∑ j', Small.goodTwist c σ (as' j) * starRingEnd ℂ (Small.goodTwist c σ (as' j')) * ipOn U W dict (xiR D) a₁ (e Z) σ (ω j) (ω j')).re = lieFacZ Dw (xiR D) a₁ ^ 2 * ThA.nrm2 ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) P`.

Simplify using `only [hip]`. Rewrite using `[re_twist _ (goodTwist_cases c σ), hT]`. Rewrite `hm` using `[hsum, Small.norm_goodTwist, hre]`. Establish `hpn : ∀ Q : Frame ((U (goodOf c σ)).X k).Ψ D.R.r → ℂ, ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) Q y = ‖Q y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y`. Introduce `Q`.

Simplify using `[Data.pnorm]`. Rewrite `hPy` using `[hpn P]`. Establish `hpos : 0 < (‖P y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y) ^ 2` using `lt_of_lt_of_le (mul_pos ht hN) hPy`. Establish `hne : ‖P y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y ≠ 0`. Introduce `h0`.

Rewrite `hpos` using `[h0]`. Simplify using `at hpos`. Establish `hPy0 : P y ≠ 0` using `fun h0 => hne (by simp [h0])`. Establish `hpn0 : 0 < ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y`. Establish `h1 : 0 ≤ ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y`.

Unfold `Data.pnorm`. Check the signs of the components of the expression. Conclude with `lt_of_le_of_ne h1 fun h0 => hne (by rw [← h0, mul_zero])`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, lin (ω j) ≠ 0 := by`. Assume the negation of the conclusion as `hc`.

Use `push_neg at hc`. Establish `h0 : Small.goodTwist c σ (P y) = 0`. Rewrite using `[← hsum]`. Simplify using `[hc]`. Conclude with `hPy0 ((map_eq_zero _).1 h0)`.

Establish `hh0 : 0 < L.h (fun x => lin (ω (ei x.2)))` using `L.pos _ fun _ => ⟨ei.symm j, by simpa using hj⟩`. Use `⟨⟨j, hj⟩, hpn0, ?_⟩` and prove the remaining obligations. Conclude with `sqrt_le_of_bounds hN hPy hm (Real.exp_pos _) hpn0 hh0`.
-/
theorem GlobalTheory.CompanionTheory.Ar.Rec.berg_dual : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r), CompLaws U h e → abelian₂.LevelLaws U W dict → FinVol W → ∀ (a₁ : WZ D.host.E) (Z : Comp Xo c) (n : ℕ) (ω : Fin n → Rul Xo c) (I : Type) [Fintype I] (L : HermLine (fun _ : Unit => I)) (ei : I ≃ Fin n), OntoZ U h e a₁ Z → Submodule.span c.F (Set.range ω) = cuspOn U h a₁ Z → ∀ (σ : c.F →+* ℂ) (k : (U (goodOf c σ)).Comp) (y : Frame ((U (goodOf c σ)).X k).Ψ D.R.r) (lin : Rul Xo c →ₛₗ[σ] ℂ), (∀ f, lin f = Small.goodTwist c σ (rdU (U (goodOf c σ)) f k y)) → (∀ as : Fin n → ℂ, ‖∑ j, as j * lin (ω j)‖ ^ 2 ≤ (∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipOn U W dict (xiR D) a₁ (e Z) σ (ω j) (ω j')).re * L.h (fun x => lin (ω (ei x.2))) ^ 2) → Over (U (goodOf c σ)) (e Z) k → y ∈ ((U (goodOf c σ)).X k).dom → ∀ (x0 : Frame ((U (goodOf c σ)).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U (goodOf c σ)).X k)))) (t : ℝ), IsOrth ((U (goodOf c σ)).X k) x0 → IsFundSet ((U (goodOf c σ)).X k) x0 FF → 0 < t → ThA.BergLB ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) y t → (∃ j, lin (ω j) ≠ 0) ∧ 0 < ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y ∧ Real.sqrt t ≤ lieFacZ Dw (xiR D) a₁ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y * L.h (fun x => lin (ω (ei x.2))) := by
  intro D H Dw l Xo c U h e W dict hL hLev hV a₁ Z n ω I _ L ei hOn hsp σ k y lin hlin hmet hOver hy x0 FF t hO hF ht hB
  have hg := goodEmb_goodOf c σ
  obtain ⟨P, hP, hN, hPy⟩ := hB
  obtain ⟨-, -, hTie⟩ := GlobalTheory.T.level_laws_frame_dictionary D H Dw l Xo c U h e W dict hL hLev hV (goodOf c σ) hg Z k hOver a₁ x0 FF hO hF
  obtain ⟨m, as, fs, hfs, hPeq⟩ := hOn (goodOf c σ) hg k hOver P hP
  have hω : ∀ j, ω j ∈ cuspOn U h a₁ Z := fun j => hsp ▸ Submodule.subset_span ⟨j, rfl⟩
  have hb : ∀ i, ∃ b : Fin n → c.F, ∑ j, b j • ω j = fs i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun c.F).1 (hsp ▸ hfs i)
  choose b hb using hb
  obtain ⟨as', has'⟩ : ∃ as' : Fin n → ℂ, as' = fun j => ∑ i, as i * goodOf c σ (b i j) := ⟨_, rfl⟩
  have hQ : ∀ x ∈ ((U (goodOf c σ)).X k).dom, P x = ∑ j, as' j * rdU (U (goodOf c σ)) (ω j) k x := by
    intro x hx
    rw [hPeq x hx]
    have e1 : ∀ i, rdU (U (goodOf c σ)) (fs i) k x = ∑ j, goodOf c σ (b i j) * rdU (U (goodOf c σ)) (ω j) k x := by
      intro i
      rw [← hb i, map_sum]
      simp [Finset.sum_apply, map_smulₛₗ]
    simp only [e1, has', Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hnrm : ThA.nrm2 ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) P =
      ThA.nrm2 ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k)
        (fun y => ∑ j, as' j * rdU (U (goodOf c σ)) (ω j) k y) := by
    unfold ThA.nrm2
    congr 1
    refine setIntegral_congr_fun hF.1 fun z hz => ?_
    simp only [Data.pnorm]
    rw [hQ _ (hF.2.1 hz)]
  have hT := hTie n as' ω hω
  rw [← hnrm] at hT
  have hm := hmet (fun j => Small.goodTwist c σ (as' j))
  have hip : ∀ f g, ipOn U W dict (xiR D) a₁ (e Z) σ f g =
      Small.goodTwist c σ (ipOn U W dict (xiR D) a₁ (e Z) (goodOf c σ) f g) := by
    intro f g
    unfold ipOn
    simp only [goodOf_goodOf, if_pos hg]
    unfold Small.goodTwist
    split_ifs <;> rfl
  have hsum : ∑ j, Small.goodTwist c σ (as' j) * lin (ω j) =
      Small.goodTwist c σ (P y) := by
    rw [hQ y hy, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hlin, map_mul]
  have hre : (∑ j, ∑ j', Small.goodTwist c σ (as' j) * starRingEnd ℂ (Small.goodTwist c σ (as' j')) *
      ipOn U W dict (xiR D) a₁ (e Z) σ (ω j) (ω j')).re = lieFacZ Dw (xiR D) a₁ ^ 2 *
        ThA.nrm2 ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) P := by
    simp only [hip]
    rw [re_twist _ (goodTwist_cases c σ), hT]
  rw [hsum, Small.norm_goodTwist, hre] at hm
  have hpn : ∀ Q : Frame ((U (goodOf c σ)).X k).Ψ D.R.r → ℂ,
      ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) Q y =
        ‖Q y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y := by
    intro Q
    simp [Data.pnorm]
  rw [hpn P] at hPy
  have hpos : 0 < (‖P y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y) ^ 2 :=
    lt_of_lt_of_le (mul_pos ht hN) hPy
  have hne : ‖P y‖ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y ≠ 0 := by
    intro h0
    rw [h0] at hpos
    simp at hpos
  have hPy0 : P y ≠ 0 := fun h0 => hne (by simp [h0])
  have hpn0 : 0 < ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y := by
    have h1 : 0 ≤ ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y := by
      unfold Data.pnorm
      positivity
    exact lt_of_le_of_ne h1 fun h0 => hne (by rw [← h0, mul_zero])
  obtain ⟨j, hj⟩ : ∃ j, lin (ω j) ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : Small.goodTwist c σ (P y) = 0 := by
      rw [← hsum]
      simp [hc]
    exact hPy0 ((map_eq_zero _).1 h0)
  have hh0 : 0 < L.h (fun x => lin (ω (ei x.2))) :=
    L.pos _ fun _ => ⟨ei.symm j, by simpa using hj⟩
  refine ⟨⟨j, hj⟩, hpn0, ?_⟩
  exact sqrt_le_of_bounds hN hPy hm (Real.exp_pos _) hpn0 hh0
