import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormApproxMultiplicityMapsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeriesStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspApproxX

open GlobalTheory.Grow GlobalTheory.Size

/- English proof (translation)
Take `⟨A, d, H⟩` from `GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank`. Take `⟨U, hU, hl⟩` from `isTheta_iff_level.1 hf`. Take `⟨μ, 𝓕, hμ⟩` from `exists_isCovolOne V W`. Take `⟨c, hc0, hc⟩` from `(H V W rfl rfl).real ψ hθ hU`. Take `⟨B, hB⟩` from `exists_height_le_of_isCompact V hC`.

Establish `key` using `(hc χS χT ω hω μ 𝓕 hμ f hl).2`. Use `set s := (sobO ψ θ μ 𝓕 d f).toReal`. Establish `hs : 0 ≤ s` using `ENNReal.toReal_nonneg`. Use `⟨c * s * max B 1 ^ A * 2 ^ A, A, fun g hg h => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ h', ‖thetaKO ω g h' f‖ ≤ (c * s * height V g ^ A) * height W h' ^ A` using `fun h' => by`.

Rewrite using `[mul_assoc _ (height V g ^ A), ← mul_pow]`. Conclude with `key g h'`. Use `(norm_le_quotHeight_pow (GlobalTheory.Chain.LiftConv.thetaKO_left hω hf g) h1 h).trans ?_` and prove the remaining obligations. Establish `hg1 : height V g ^ A ≤ max B 1 ^ A` using `pow_le_pow_left₀ (height_pos V g).le ((hB g hg).trans (le_max_left _ _)) A`. Establish `hq` using `(pow_pos (quotHeight_pos W h) A).le`.

Establish `h2 : (0:ℝ) ≤ 2 ^ A` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem thetaKO_le_quotHeight {D : D7} {V W : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)} {f : WO V W → ℂ}
    (hθ : IsInfFam θ) (hω : IsWeilDatumO ψ V W χS χT ω) (hf : IsThetaFunO ψ V W f) {C : Set (GA D V)}
    (hC : IsCompact C) : ∃ (K : ℝ) (a : ℕ), ∀ g ∈ C, ∀ h, ‖thetaKO ω g h f‖ ≤ K * quotHeight W h ^ a := by
  obtain ⟨A, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D V.rank W.rank
  obtain ⟨U, hU, hl⟩ := isTheta_iff_level.1 hf
  obtain ⟨μ, 𝓕, hμ⟩ := exists_isCovolOne V W
  obtain ⟨c, hc0, hc⟩ := (H V W rfl rfl).real ψ hθ hU
  obtain ⟨B, hB⟩ := exists_height_le_of_isCompact V hC
  have key := (hc χS χT ω hω μ 𝓕 hμ f hl).2
  set s := (sobO ψ θ μ 𝓕 d f).toReal
  have hs : 0 ≤ s := ENNReal.toReal_nonneg
  refine ⟨c * s * max B 1 ^ A * 2 ^ A, A, fun g hg h => ?_⟩
  have h1 : ∀ h', ‖thetaKO ω g h' f‖ ≤ (c * s * height V g ^ A) * height W h' ^ A := fun h' => by
    rw [mul_assoc _ (height V g ^ A), ← mul_pow]; exact key g h'
  refine (norm_le_quotHeight_pow (GlobalTheory.Chain.LiftConv.thetaKO_left hω hf g) h1 h).trans ?_
  have hg1 : height V g ^ A ≤ max B 1 ^ A :=
    pow_le_pow_left₀ (height_pos V g).le ((hB g hg).trans (le_max_left _ _)) A
  have hq := (pow_pos (quotHeight_pos W h) A).le
  have h2 : (0:ℝ) ≤ 2 ^ A := by positivity
  calc c * s * height V g ^ A * 2 ^ A * quotHeight W h ^ A
      ≤ c * s * max B 1 ^ A * 2 ^ A * quotHeight W h ^ A := by gcongr
    _ = _ := rfl

end GlobalTheory.CuspApproxX

namespace GlobalTheory.CuspApproxX

open GlobalTheory.Grow GlobalTheory.Size

/- English proof (translation)
Introduce `_hL hP D _hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC ε hε`. Establish `hM` using `GlobalTheory.PairLift.haar_vert hRB hG t hi.le hj`. Establish `: BorelSpace (GA D (G.V i j).V)` using `⟨rfl⟩`. Establish `hw` using `(hG.arrows.X i j hi hj).weil`. Take `⟨K, a, hK⟩` from `thetaKO_le_quotHeight hRB.inf hw hΦ (hC.image (GlobalTheory.Grid.continuous_ofSgn_symm true (G.V (i + 1) j).V))`.

Establish `hK' : ∀ h ∈ C, ∀ g, ‖thetaKO (G.X i j).ω h g Φ‖ ≤ |K| * quotHeight (G.V i j).V g ^ a`. Introduce `h hh g`. Establish `key` using `hK _ ⟨h, hh, rfl⟩ g`. Use `le_trans (le_of_eq ?_) (key.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (pow_pos (quotHeight_pos _ g) a).le))` and prove the remaining obligations. Use `congr 1`.

Establish `hI : ∀ ψ' : GA D (G.V i j).V → ℂ, RapidDec (G.V i j).V ψ' → ∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * ψ' g) (G.meas t i j).fd (G.meas t i j).ν`. Introduce `ψ' hr h`. Establish `key` using `GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec (GlobalTheory.KernelSeminorm.thetaGrowth D) hRB.inf hw hΦ hM.1 hM.2 hr ((GlobalTheory.Grid.ofSgn true _).symm h)`. Use `key using 3 with g` and compare the differences between its conclusion and the goal. Simplify using `only [thetaKO, GlobalTheory.Grid.WRep.toSgn, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, MonoidHom.id_apply]`.

Establish `hfin` using `GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hM.1 hM.2`. Use `set vol := (G.meas t i j).ν.real (G.meas t i j).fd with hvol`. Establish `hv0 : 0 ≤ vol` using `measureReal_nonneg`. Use `set δ := ε / (2 * ((|K| + 1) * (vol + 1))) with hδ`. Establish `hpos : 0 < 2 * ((|K| + 1) * (vol + 1))` using `by positivity`.

Establish `hδ0 : 0 < δ` using `div_pos hε hpos`. Take `⟨n, Tm, v, hT, hap⟩` from `happrox hP D G₀ Pl0 T A Ks R G hRB hG i j hi.le hj φ hφ a δ hδ0`. Establish `hval : ∀ l, (PiTensorProduct.lift (Tm l)) (PiTensorProduct.tprod ℂ (v l)) = Tm l (v l)` using `fun l => PiTensorProduct.lift.tprod _`. Establish `hR : ∀ l, RapidDec (G.V i j).V (Tm l (v l))` using `fun l => rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf ((hT l).aut (v l)) ((hT l).cusp (v l))`. Use `⟨n, fun l => PiTensorProduct.lift (Tm l), fun l => PiTensorProduct.tprod ℂ (v l), fun l => ?_, fun l h => ?_, fun h hh => ?_⟩` and prove the remaining obligations.

Rewrite using `[Formalism.IndefR.Mult.mem_multT, LinearEquiv.symm_apply_apply]`. Conclude with `Submodule.subset_span (hT l)`. Rewrite using `[hval]`. Conclude with `hI _ (hR l) h`. Simplify using `only [hval]`.

Establish `hIl : ∀ l, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * Tm l (v l) g) (G.meas t i j).fd (G.meas t i j).ν` using `fun l => hI _ (hR l) h`. Rewrite using `[← integral_finsetSum _ fun l _ => hIl l, ← integral_sub (hint h) (integrable_finsetSum _ fun l _ => hIl l)]`. Establish `hb : ∀ g ∈ (G.meas t i j).fd, ‖thetaKO (G.X i j).ω h g Φ * φ g - ∑ l, thetaKO (G.X i j).ω h g Φ * Tm l (v l) g‖ ≤ |K| * δ`. Introduce `g _`. Rewrite using `[← Finset.mul_sum, ← mul_sub, norm_mul]`.

Establish `h1` using `hK' h hh g`. Establish `h2` using `hap g`. Establish `hq` using `(pow_pos (quotHeight_pos (G.V i j).V g) a).le`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_setIntegral_le_of_norm_le_const hfin hb).trans_lt ?_` and prove the remaining obligations.

Rewrite using `[← hvol]`. Establish `e : |K| * δ * vol ≤ (|K| + 1) * (vol + 1) * δ`. Establish `: |K| * vol ≤ (|K| + 1) * (vol + 1)` using `by nlinarith [abs_nonneg K]`. Use the polynomial consequences of the given equalities and inequalities. Establish `e2 : (|K| + 1) * (vol + 1) * δ = ε / 2`.

Rewrite using `[hδ]`. Clear the denominators using the available nonvanishing facts. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem approx_lift (happrox : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ (n : ℕ) (T : Fin n → Formalism.IndefR.Mult.MMap (G.V i j).M) (v : Fin n → (G.V i j).M.Vec), (∀ l, Formalism.IndefR.Mult.IsMultMap R.θ (G.V i j).M ∅ 1 (T l)) ∧ ∀ g, ‖φ g - ∑ l, T l (v l) g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F l (v l) g) (G.meas t i j).fd (G.meas t i j).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F l (v l) g ∂(G.meas t i j).ν‖ < ε := by
  intro _hL hP D _hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC ε hε
  have hM := GlobalTheory.PairLift.haar_vert hRB hG t hi.le hj
  have : BorelSpace (GA D (G.V i j).V) := ⟨rfl⟩
  have hw := (hG.arrows.X i j hi hj).weil

  obtain ⟨K, a, hK⟩ := thetaKO_le_quotHeight hRB.inf hw hΦ
    (hC.image (GlobalTheory.Grid.continuous_ofSgn_symm true (G.V (i + 1) j).V))
  have hK' : ∀ h ∈ C, ∀ g, ‖thetaKO (G.X i j).ω h g Φ‖ ≤ |K| * quotHeight (G.V i j).V g ^ a := by
    intro h hh g
    have key := hK _ ⟨h, hh, rfl⟩ g
    refine le_trans (le_of_eq ?_) (key.trans (mul_le_mul_of_nonneg_right (le_abs_self K)
      (pow_pos (quotHeight_pos _ g) a).le))
    congr 1

  have hI : ∀ ψ' : GA D (G.V i j).V → ℂ, RapidDec (G.V i j).V ψ' → ∀ h,
      IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * ψ' g) (G.meas t i j).fd (G.meas t i j).ν := by
    intro ψ' hr h
    have key := GlobalTheory.Chain.LiftConv.integrableOn_of_rapidDec (GlobalTheory.KernelSeminorm.thetaGrowth D) hRB.inf hw hΦ hM.1
      hM.2 hr ((GlobalTheory.Grid.ofSgn true _).symm h)
    convert key using 3 with g
    simp only [thetaKO, GlobalTheory.Grid.WRep.toSgn, MonoidHom.comp_apply, MonoidHom.prodMap, MonoidHom.prod_apply,
      MonoidHom.coe_comp, Function.comp_apply, MonoidHom.coe_fst, MonoidHom.coe_snd, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, MonoidHom.id_apply]
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol _ _ _ hM.1 hM.2
  set vol := (G.meas t i j).ν.real (G.meas t i j).fd with hvol
  have hv0 : 0 ≤ vol := measureReal_nonneg
  set δ := ε / (2 * ((|K| + 1) * (vol + 1))) with hδ
  have hpos : 0 < 2 * ((|K| + 1) * (vol + 1)) := by positivity
  have hδ0 : 0 < δ := div_pos hε hpos
  obtain ⟨n, Tm, v, hT, hap⟩ := happrox hP D G₀ Pl0 T A Ks R G hRB hG i j hi.le hj φ hφ a δ hδ0
  have hval : ∀ l, (PiTensorProduct.lift (Tm l)) (PiTensorProduct.tprod ℂ (v l)) = Tm l (v l) := fun l =>
    PiTensorProduct.lift.tprod _
  have hR : ∀ l, RapidDec (G.V i j).V (Tm l (v l)) := fun l =>
    rapidDec_of_cuspForm hP.cuspRapidDecay hRB.inf ((hT l).aut (v l)) ((hT l).cusp (v l))
  refine ⟨n, fun l => PiTensorProduct.lift (Tm l), fun l => PiTensorProduct.tprod ℂ (v l), fun l => ?_, fun l h => ?_,
    fun h hh => ?_⟩
  · rw [Formalism.IndefR.Mult.mem_multT, LinearEquiv.symm_apply_apply]
    exact Submodule.subset_span (hT l)
  · rw [hval]; exact hI _ (hR l) h
  · simp only [hval]
    have hIl : ∀ l, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * Tm l (v l) g) (G.meas t i j).fd
        (G.meas t i j).ν := fun l => hI _ (hR l) h
    rw [← integral_finsetSum _ fun l _ => hIl l, ← integral_sub (hint h) (integrable_finsetSum _ fun l _ => hIl l)]
    have hb : ∀ g ∈ (G.meas t i j).fd, ‖thetaKO (G.X i j).ω h g Φ * φ g -
        ∑ l, thetaKO (G.X i j).ω h g Φ * Tm l (v l) g‖ ≤ |K| * δ := by
      intro g _
      rw [← Finset.mul_sum, ← mul_sub, norm_mul]
      have h1 := hK' h hh g
      have h2 := hap g
      have hq := (pow_pos (quotHeight_pos (G.V i j).V g) a).le
      calc ‖thetaKO (G.X i j).ω h g Φ‖ * ‖φ g - ∑ l, Tm l (v l) g‖
          ≤ |K| * quotHeight (G.V i j).V g ^ a * ‖φ g - ∑ l, Tm l (v l) g‖ :=
            mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
        _ = |K| * (‖φ g - ∑ l, Tm l (v l) g‖ * quotHeight (G.V i j).V g ^ a) := by ring
        _ ≤ |K| * δ := mul_le_mul_of_nonneg_left h2 (abs_nonneg K)
    refine (norm_setIntegral_le_of_norm_le_const hfin hb).trans_lt ?_
    rw [← hvol]
    have e : |K| * δ * vol ≤ (|K| + 1) * (vol + 1) * δ := by
      have : |K| * vol ≤ (|K| + 1) * (vol + 1) := by nlinarith [abs_nonneg K]
      nlinarith
    have e2 : (|K| + 1) * (vol + 1) * δ = ε / 2 := by
      rw [hδ]; field_simp
    linarith

end GlobalTheory.CuspApproxX

namespace GlobalTheory.CuspApproxX

/- English proof (translation)
The claim follows from `approx_lift GlobalTheory.T.cusp_form_approx_multiplicity_maps`.
-/
theorem approx_lift_main : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ (∀ l h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * F l (v l) g) (G.meas t i j).fd (G.meas t i j).ν) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * F l (v l) g ∂(G.meas t i j).ν‖ < ε :=
  approx_lift GlobalTheory.T.cusp_form_approx_multiplicity_maps

end GlobalTheory.CuspApproxX

end
