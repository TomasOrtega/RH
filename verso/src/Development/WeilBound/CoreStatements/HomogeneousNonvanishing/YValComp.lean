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
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CompactificationCompEquiv
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsNormalChartsOfCoveringCharts
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace PositivityTheory.UnitarySelfGeneration

namespace YValComp

/- English proof (translation)
Use `haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)`. Establish `h1 : (⊥ : Ideal R).jacobson = ⊥` using `IsJacobsonRing.out inferInstance Ideal.isPrime_bot.isRadical`. Choose the witnesses or unpack the hypotheses as in `⟨m, hm, hh⟩ : ∃ m : Ideal R, m.IsMaximal ∧ h ∉ m := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Establish `: h ∈ (⊥ : Ideal R).jacobson` using `Ideal.mem_sInf.2 fun J hJ => hcon _ hJ.2`. Rewrite `this` using `[h1]`. Conclude with `h0 this`. Use `letI := Ideal.Quotient.field m`. Use `haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)`.

Conclude with `⟨R ⧸ m, inferInstance, NumberField.of_module_finite K _, inferInstance, Ideal.Quotient.mkₐ K m, fun e => hh (Ideal.Quotient.eq_zero_iff_mem.1 e)⟩`.
-/
theorem exists_alg_pt {K R : Type} [Field K] [NumberField K] [CommRing R] [IsDomain R] [Algebra K R]
    [Algebra.FiniteType K R] {h : R} (h0 : h ≠ 0) :
    ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (ψ : R →ₐ[K] K'), ψ h ≠ 0 := by
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K)
  have h1 : (⊥ : Ideal R).jacobson = ⊥ := IsJacobsonRing.out inferInstance Ideal.isPrime_bot.isRadical
  obtain ⟨m, hm, hh⟩ : ∃ m : Ideal R, m.IsMaximal ∧ h ∉ m := by
    by_contra hcon
    push Not at hcon
    have : h ∈ (⊥ : Ideal R).jacobson := Ideal.mem_sInf.2 fun J hJ => hcon _ hJ.2
    rw [h1] at this
    exact h0 this
  letI := Ideal.Quotient.field m
  haveI : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  exact ⟨R ⧸ m, inferInstance, NumberField.of_module_finite K _, inferInstance, Ideal.Quotient.mkₐ K m,
    fun e => hh (Ideal.Quotient.eq_zero_iff_mem.1 e)⟩

/- English proof (translation)
Establish `: w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal` using `⟨rfl⟩`. Use `⟨e * (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal, Nat.mul_pos ho.1 (Nat.pos_of_ne_zero (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot)), fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.comp_apply, ho.2, vLa, vLa, ← HeightOneSpectrum.valuation_liesOver L (w.under (𝓞 K)) w a, WithZero.log_pow]`. Simplify using `[mul_assoc]`.
-/
theorem overLa_comp {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    {w : HeightOneSpectrum (𝓞 L)} {V : CDVR} {ι : L →+* V.Fr} {e : ℕ} (ho : OverLa w V.V ι e) :
    ∃ e', OverLa (w.under (𝓞 K)) V.V (ι.comp (algebraMap K L)) e' := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  refine ⟨e * (w.under (𝓞 K)).asIdeal.ramificationIdx' w.asIdeal, Nat.mul_pos ho.1 (Nat.pos_of_ne_zero
    (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 K)).ne_bot)), fun a => ?_⟩
  rw [RingHom.comp_apply, ho.2, vLa, vLa, ← HeightOneSpectrum.valuation_liesOver L (w.under (𝓞 K)) w a,
    WithZero.log_pow]
  simp [mul_assoc]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

/- English proof (translation)
Use `⟨⟨⟨differentiableOn_const 0, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩, 0, fun x _ => (pnorm_zero X la x).le⟩, fun ξ _ x _ => ?_⟩` and prove the remaining obligations. Unfold `Data.fj`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem zero_mem_SS (X : Data E r) (la : Wt X.Ψ r) : (0 : Frame X.Ψ r → ℂ) ∈ X.SS la := by
  refine ⟨⟨⟨differentiableOn_const 0, fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩, 0,
    fun x _ => (pnorm_zero X la x).le⟩, fun ξ _ x _ => ?_⟩
  unfold Data.fj
  split_ifs <;> simp

open Classical in
/- English proof (translation)
Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem P hP`. Use `Submodule.subset_span fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : k = k₀`. Simplify using `only [if_pos hk]`.

Conclude with `hP k`. Simplify using `only [hk, if_false]`. Conclude with `zero_mem_SS _ _`. Consider the case `zero`. Use `(holSub X la).zero_mem using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `k`. Simplify using the standard rewrite rules. Consider the case `add P Q _ _ hP hQ`. Use `(holSub X la).add_mem hP hQ using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext k; by_cases hk : k = k₀ <;> simp [hk]`.

Consider the case `smul a P _ hP`. Use `(holSub X la).smul_mem a hP using 1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `funext k; by_cases hk : k = k₀ <;> simp [hk]`.
-/
theorem cut_mem {Cp : Type} (X : Cp → Data E r) (la : ∀ k, Wt (X k).Ψ r) (k₀ : Cp) {P : FDSec X}
    (hP : P ∈ holSub X la) : (fun k => if k = k₀ then P k else 0 : FDSec X) ∈ holSub X la := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    refine Submodule.subset_span fun k => ?_
    by_cases hk : k = k₀
    · simp only [if_pos hk]; exact hP k
    · simp only [hk, if_false]; exact zero_mem_SS _ _
  | zero =>
    convert (holSub X la).zero_mem using 1
    funext k; simp
  | add P Q _ _ hP hQ =>
    convert (holSub X la).add_mem hP hQ using 1
    funext k; by_cases hk : k = k₀ <;> simp [hk]
  | smul a P _ hP =>
    convert (holSub X la).smul_mem a hP using 1
    funext k; by_cases hk : k = k₀ <;> simp [hk]

/- English proof (translation)
Rewrite using `[GlobalTheory.FlagTan.evR_frBor (mem_allWt_of_secZ (CompOver.mem_secZ_zero hf)) h]`. Apply the tactic sequence `have h0 : ∀ i, Rec.exZ Dw 0 i = 0 := fun i => by cases i <;> rfl`. Simplify using `[h0]`.
-/
theorem evR_invariant_borel_translate {S : Type} [Field S] [Algebra c.F S] {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0) {t : Ix Dw → Sˣ}
    {y y' : FrPt Xo c S} (h : FrBor t y y') : evR Xo c f y' = evR Xo c f y := by
  rw [GlobalTheory.FlagTan.evR_frBor (mem_allWt_of_secZ (CompOver.mem_secZ_zero hf)) h]
  have h0 : ∀ i, Rec.exZ Dw 0 i = 0 := fun i => by cases i <;> rfl
  simp [h0]

/- English proof (translation)
Simplify using `only [cuspOn, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, evL_apply]`.
-/
theorem mem_cuspOn {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {a : WZ E} {Z : Comp Xo c} {f : Rul Xo c} :
    f ∈ cuspOn U h a Z ↔ f ∈ Rec.cuspZ Xo c U a ∧ ∀ Z', Z' ≠ Z → evC h Z' f = 0 := by
  simp only [cuspOn, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, evL_apply]

/- English proof (translation)
Simplify using `only [Rec.cuspZ, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]`.
-/
theorem mem_cuspZ {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {a : WZ E} {f : Rul Xo c} :
    f ∈ Rec.cuspZ Xo c U a ↔ f ∈ Rec.secZ Xo c a ∧
      ∀ σ, GoodEmb c σ → rdU (U σ) f ∈ holSub (U σ).X (Rec.laZ (U σ) a) := by
  simp only [Rec.cuspZ, Submodule.mem_inf, Submodule.mem_iInf, Submodule.mem_comap]

/- English proof (translation)
Rewrite using `[nval_of_ne one_ne_zero]`. Simplify using `[vV]`.
-/
theorem nval_one {V K' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K']
    [Algebra V K'] [IsFractionRing V K'] (d : ℕ) : nval V d (1 : K') = 0 := by
  rw [nval_of_ne one_ne_zero]; simp [vV]

/- English proof (translation)
Take `⟨i1, -, i3, i4, i5, i6⟩` from `sections_generic_indicators E H Dw l Xo c r U h e L`. Establish `hfin : Finite (Comp Xo c)` using `Formalism.L2.Pj.CompFin.finite_comp Xo c`. Set `` to `Fintype.ofFinite (Comp Xo c)`. Rewrite `i6` using `[finsum_eq_sum_of_fintype]`. Introduce and unpack `la _ ⟨⟨_, T, io, d, ho, y, -, η, -, rfl⟩, rfl⟩`.

Set `` to `io.toAlgebra`. Set `ev` to `CompOver.evA y.1 y.2.1`. Choose the witnesses or unpack the hypotheses as in `⟨Z, hZ⟩ : ∃ Z, ev (e Z) ≠ 0 := by`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Use `congrArg ev i6` as an intermediate fact. Rewrite `this` using `[map_sum, map_one]`. Simplify using `[hcon] at this`. Establish `h1 : ev (e Z) = 1` using `mul_left_cancel₀ hZ (by rw [← map_mul, i4, mul_one])`. Establish `h2 : ∀ f, f * e Z = 0 → nval T.V d (evI y f) = ⊤` using `fun f hf => by`.

Use `congrArg ev hf` as an intermediate fact. Rewrite `this` using `[map_mul, h1, mul_one, map_zero]`. Use `show nval T.V d (ev f) = ⊤`. Rewrite using `[this, nval_zero]`. Use `⟨Z, ?_, fun Z' hne => ⟨h2 _ (i5 _ _ hne), fun a f hf => h2 f ?_⟩⟩` and prove the remaining obligations.

Use `show nval T.V d (ev (e Z)) = 0`. Rewrite using `[h1, nval_one]`. Take `⟨hf1, hf2⟩` from `mem_cuspOn.1 hf`. Use `i1 (a + 0) _ (i3 a 0 f (mem_cuspZ.1 hf1).1 _ (CompOver.mem_secZ_zero (L.e_sec Z))) fun W => ?_` and prove the remaining obligations. Rewrite using `[evC_mul_of_test L.genT]`.

Distinguish the cases in `hW : W = Z`. Substitute `hW` using the available equality. Rewrite using `[hf2 _ hne.symm, zero_mul]`. Rewrite using `[(L.e_val Z).2 W hW, mul_zero]`.
-/
theorem part1 {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c} (L : CompLaws U h e) :
    ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, ∃ Z, v (e Z) = 0 ∧ ∀ Z', Z' ≠ Z → v (e Z') = ⊤ ∧
      ∀ a, ∀ f ∈ cuspOn U h a Z', v f = ⊤ := by
  obtain ⟨i1, -, i3, i4, i5, i6⟩ := sections_generic_indicators E H Dw l Xo c r U h e L
  have hfin : Finite (Comp Xo c) := Formalism.L2.Pj.CompFin.finite_comp Xo c
  let := Fintype.ofFinite (Comp Xo c)
  rw [finsum_eq_sum_of_fintype] at i6
  rintro la _ ⟨⟨_, T, io, d, ho, y, -, η, -, rfl⟩, rfl⟩
  let := io.toAlgebra
  let ev := CompOver.evA y.1 y.2.1
  obtain ⟨Z, hZ⟩ : ∃ Z, ev (e Z) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := congrArg ev i6
    rw [map_sum, map_one] at this
    simp [hcon] at this
  have h1 : ev (e Z) = 1 := mul_left_cancel₀ hZ (by rw [← map_mul, i4, mul_one])
  have h2 : ∀ f, f * e Z = 0 → nval T.V d (evI y f) = ⊤ := fun f hf => by
    have := congrArg ev hf
    rw [map_mul, h1, mul_one, map_zero] at this
    show nval T.V d (ev f) = ⊤
    rw [this, nval_zero]
  refine ⟨Z, ?_, fun Z' hne => ⟨h2 _ (i5 _ _ hne), fun a f hf => h2 f ?_⟩⟩
  · show nval T.V d (ev (e Z)) = 0
    rw [h1, nval_one]
  · obtain ⟨hf1, hf2⟩ := mem_cuspOn.1 hf
    refine i1 (a + 0) _ (i3 a 0 f (mem_cuspZ.1 hf1).1 _ (CompOver.mem_secZ_zero (L.e_sec Z))) fun W => ?_
    rw [evC_mul_of_test L.genT]
    by_cases hW : W = Z
    · subst hW
      rw [hf2 _ hne.symm, zero_mul]
    · rw [(L.e_val Z).2 W hW, mul_zero]

/- English proof (translation)
Introduce `la Z`. Take `⟨-, -, -, i4, -, -⟩` from `sections_generic_indicators E H Dw l Xo c r U h e L`. Take `⟨hE, -, -, hA⟩` from `GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c`. Take `⟨C, ψ, z, t, hz, hb⟩` from `hA h _ (genFr h Z)`. Establish `hs` using `L.e_sec Z`.

Establish `h1 : ψ (evR Xo c (e Z) C.y) = 1`. Rewrite using `[← GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hE 0 0 _ hs _ _ ψ _ _ hz, ← evR_invariant_borel_translate hs hb]`. Conclude with `(L.e_val Z).1`. Establish `h2 : evR Xo c (e Z) C.y ≠ 0` using `fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1`. Use `C.sm` as an intermediate fact.

Take `⟨K, _, _, _, ψ₀, hψ₀⟩` from `exists_alg_pt (K := c.F) h2`. Use `la.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hQl⟩` from `Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) la.asIdeal (by`. Rewrite using `[(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 c.F) (𝓞 K))]`. Conclude with `bot_le)`.

Establish `hQ0 : Q ≠ ⊥`. Introduce and unpack `rfl`. Apply `la.ne_bot` to reduce the goal to its premises. Rewrite using `[← hQl]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 c.F) (𝓞 K))`.

Set `w : HeightOneSpectrum (𝓞 K)` to `⟨Q, hQ.isPrime, hQ0⟩`. Establish `hw : w.under (𝓞 c.F) = la` using `HeightOneSpectrum.ext hQl`. Take `⟨T, κ, ho, hfin, -⟩` from `GlobalTheory.PlaceCompletion.exists_initial_completion K w`. Take `⟨e', ho'⟩` from `overLa_comp (K := c.F) ho`. Rewrite `ho'` using `[hw]`.

Set `io : c.F →+* T.Fr` to `κ.comp (algebraMap c.F K)`. Set `: Algebra c.F T.Fr` to `io.toAlgebra`. Set `κ' : K →ₐ[c.F] T.Fr` to `{ κ with commutes' := fun _ => rfl }`. Take `⟨y₀, hy₀⟩` from `hE.bc _ _ (κ'.comp ψ₀) C.y`. Establish `h3 : evR Xo c (e Z) y₀ ≠ 0`.

Rewrite using `[GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hE 0 0 _ hs _ _ _ _ _ hy₀]`. Conclude with `(map_ne_zero κ).2 hψ₀`. Take `⟨T', io', d, y', ho'', halg, hrest⟩` from `L.intAll la T io e' ho' hfin y₀`. Set `` to `io'.toAlgebra`. Take `⟨φ, z', t', -, hz', hb'⟩` from `hrest`.

Establish `h4 : evI y' (e Z) ≠ 0` using `by show evR Xo c (e Z) y'.1 ≠ 0`. Rewrite using `[evR_invariant_borel_translate hs hb', GlobalTheory.FlagTan.evR_frMap hs.1 hz']`. Conclude with `(map_ne_zero φ).2 h3`. Establish `h5 : evI y' (e Z) = 1` using `mul_left_cancel₀ h4 (by rw [← evI_mul, i4, mul_one])`. Use `⟨_, ⟨PtV.mk (cls := algCls Xo c) (PY := Unit) (lies := fun _ _ _ _ => True) la ho'' y' halg () trivial, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `show nval T'.V d (evI y' (e Z)) = 0`. Rewrite using `[h5, nval_one]`.
-/
theorem part2 {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c} (L : CompLaws U h e) :
    ∀ la Z, ∃ v ∈ valSet Xo c (algCls Xo c) la, v (e Z) = 0 := by
  intro la Z
  obtain ⟨-, -, -, i4, -, -⟩ := sections_generic_indicators E H Dw l Xo c r U h e L
  obtain ⟨hE, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h _ (genFr h Z)
  have hs := L.e_sec Z
  have h1 : ψ (evR Xo c (e Z) C.y) = 1 := by
    rw [← GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hE 0 0 _ hs _ _ ψ _ _ hz, ← evR_invariant_borel_translate hs hb]
    exact (L.e_val Z).1
  have h2 : evR Xo c (e Z) C.y ≠ 0 := fun h0 => by rw [h0, map_zero] at h1; exact zero_ne_one h1
  have := C.sm
  obtain ⟨K, _, _, _, ψ₀, hψ₀⟩ := exists_alg_pt (K := c.F) h2
  have := la.isMaximal
  obtain ⟨Q, hQ, hQl⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) la.asIdeal (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective (𝓞 c.F) (𝓞 K))]; exact bot_le)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply la.ne_bot
    rw [← hQl]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 c.F) (𝓞 K))
  let w : HeightOneSpectrum (𝓞 K) := ⟨Q, hQ.isPrime, hQ0⟩
  have hw : w.under (𝓞 c.F) = la := HeightOneSpectrum.ext hQl
  obtain ⟨T, κ, ho, hfin, -⟩ := GlobalTheory.PlaceCompletion.exists_initial_completion K w
  obtain ⟨e', ho'⟩ := overLa_comp (K := c.F) ho
  rw [hw] at ho'
  let io : c.F →+* T.Fr := κ.comp (algebraMap c.F K)
  let : Algebra c.F T.Fr := io.toAlgebra
  let κ' : K →ₐ[c.F] T.Fr := { κ with commutes' := fun _ => rfl }
  obtain ⟨y₀, hy₀⟩ := hE.bc _ _ (κ'.comp ψ₀) C.y
  have h3 : evR Xo c (e Z) y₀ ≠ 0 := by
    rw [GlobalTheory.Reg.evR_baseChange_of_isReduced E H Dw l Xo c hE 0 0 _ hs _ _ _ _ _ hy₀]
    exact (map_ne_zero κ).2 hψ₀
  obtain ⟨T', io', d, y', ho'', halg, hrest⟩ := L.intAll la T io e' ho' hfin y₀
  let := io'.toAlgebra
  obtain ⟨φ, z', t', -, hz', hb'⟩ := hrest
  have h4 : evI y' (e Z) ≠ 0 := by
    show evR Xo c (e Z) y'.1 ≠ 0
    rw [evR_invariant_borel_translate hs hb', GlobalTheory.FlagTan.evR_frMap hs.1 hz']
    exact (map_ne_zero φ).2 h3
  have h5 : evI y' (e Z) = 1 := mul_left_cancel₀ h4 (by rw [← evI_mul, i4, mul_one])
  refine ⟨_, ⟨PtV.mk (cls := algCls Xo c) (PY := Unit) (lies := fun _ _ _ _ => True) la ho'' y' halg () trivial, rfl⟩,
    ?_⟩
  show nval T'.V d (evI y' (e Z)) = 0
  rw [h5, nval_one]

/- English proof (translation)
Introduce `f hf`. Take `⟨hf1, hf2⟩` from `mem_cuspZ.1 hf`. Use `mem_cuspOn.2 ⟨mem_cuspZ.2 ⟨?_, fun σ hσ => ?_⟩, fun Z' hne => ?_⟩` and prove the remaining obligations. Use `secZ_mul (CompOver.mem_secZ_zero (L.e_sec Z)) hf1` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.

Take `⟨κ, h1, h2⟩` from `comp_over E H Dw l Xo c r U h e L σ hσ`. Use `cut_mem _ _ (κ Z) (hf2 σ hσ) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[GlobalTheory.AllWt.rdU_mul]`. Use function extensionality and compare the values at `k x`. Distinguish the cases in `hx : x ∈ ((U σ).X k).dom`.

Distinguish the cases in `hk : k = κ Z`. Rewrite using `[if_pos hk, Pi.mul_apply, Pi.mul_apply, (h1 Z k).2 hk x hx, one_mul]`. Rewrite using `[if_neg hk, Pi.mul_apply, Pi.mul_apply, (h2 Z k hk x hx).1, zero_mul]`. Both sides reduce to the same expression. Establish `: rdU (U σ) f k x = 0` using `by simp [rdU, hx]`.

Rewrite using `[Pi.mul_apply, Pi.mul_apply, this, mul_zero]`. Use `split_ifs`. Conclude with `this.symm`. Both sides reduce to the same expression. Rewrite using `[evC_mul_of_test L.genT, (L.e_val Z).2 Z' hne, zero_mul]`.
-/
theorem part3 {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {h : GenFrEx Xo c} {e : Comp Xo c → Rul Xo c} (L : CompLaws U h e)
    (a : WZ E) (Z : Comp Xo c) : ∀ f ∈ Rec.cuspZ Xo c U a, e Z * f ∈ cuspOn U h a Z := by
  classical
  intro f hf
  obtain ⟨hf1, hf2⟩ := mem_cuspZ.1 hf
  refine mem_cuspOn.2 ⟨mem_cuspZ.2 ⟨?_, fun σ hσ => ?_⟩, fun Z' hne => ?_⟩
  · have := secZ_mul (CompOver.mem_secZ_zero (L.e_sec Z)) hf1
    rwa [zero_add] at this
  · obtain ⟨κ, h1, h2⟩ := comp_over E H Dw l Xo c r U h e L σ hσ
    convert cut_mem _ _ (κ Z) (hf2 σ hσ) using 1
    rw [GlobalTheory.AllWt.rdU_mul]
    funext k x
    by_cases hx : x ∈ ((U σ).X k).dom
    · by_cases hk : k = κ Z
      · rw [if_pos hk, Pi.mul_apply, Pi.mul_apply, (h1 Z k).2 hk x hx, one_mul]
      · rw [if_neg hk, Pi.mul_apply, Pi.mul_apply, (h2 Z k hk x hx).1, zero_mul]; rfl
    · have : rdU (U σ) f k x = 0 := by simp [rdU, hx]
      rw [Pi.mul_apply, Pi.mul_apply, this, mul_zero]
      split_ifs
      · exact this.symm
      · rfl
  · rw [evC_mul_of_test L.genT, (L.e_val Z).2 Z' hne, zero_mul]

end YValComp

open YValComp in
/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c r U h e L`. Use `⟨part1 L, part2 L, fun a => ⟨part3 L a, le_antisymm (iSup_le fun Z => inf_le_left) fun f hf => ?_⟩⟩` and prove the remaining obligations. Take `⟨-, -, -, -, -, i6⟩` from `sections_generic_indicators E H Dw l Xo c r U h e L`. Establish `hfin : Finite (Comp Xo c)` using `Formalism.L2.Pj.CompFin.finite_comp Xo c`. Set `` to `Fintype.ofFinite (Comp Xo c)`.

Rewrite `i6` using `[finsum_eq_sum_of_fintype]`. Rewrite using `[← one_mul f, ← i6, Finset.sum_mul]`. Conclude with `Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z (part3 L a Z f hf)`.
-/
theorem y_val_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → (∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, ∃ Z, v (e Z) = 0 ∧ ∀ Z', Z' ≠ Z → v (e Z') = ⊤ ∧ ∀ a, ∀ f ∈ cuspOn U h a Z', v f = ⊤) ∧ (∀ la Z, ∃ v ∈ valSet Xo c (algCls Xo c) la, v (e Z) = 0) ∧ ∀ a, (∀ Z, ∀ f ∈ cuspZ Xo c U a, e Z * f ∈ cuspOn U h a Z) ∧ ⨆ Z, cuspOn U h a Z = cuspZ Xo c U a := by
  intro E _ _ _ H Dw l Xo c r U h e L
  refine ⟨part1 L, part2 L, fun a => ⟨part3 L a, le_antisymm (iSup_le fun Z => inf_le_left) fun f hf => ?_⟩⟩
  obtain ⟨-, -, -, -, -, i6⟩ := sections_generic_indicators E H Dw l Xo c r U h e L
  have hfin : Finite (Comp Xo c) := Formalism.L2.Pj.CompFin.finite_comp Xo c
  let := Fintype.ofFinite (Comp Xo c)
  rw [finsum_eq_sum_of_fintype] at i6
  rw [← one_mul f, ← i6, Finset.sum_mul]
  exact Submodule.sum_mem _ fun Z _ => Submodule.mem_iSup_of_mem Z (part3 L a Z f hf)

end PositivityTheory.UnitarySelfGeneration
