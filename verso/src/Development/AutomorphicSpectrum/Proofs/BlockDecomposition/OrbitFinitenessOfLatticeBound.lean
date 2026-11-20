import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaFiniteParameterProductMeasure
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSchwartzBruhatAdelicMatrixOfMemAdelicSchwartz
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.CompanionTheory.ColumnSplitting

/- English proof (translation)
Introduce `hL D θ hθ W m hm x₀ hx N hN`. Take `⟨C, hC⟩` from `hL D θ hθ W W.rank N hN`. Establish `hB : BorelSpace (GA D W)` using `⟨rfl⟩`. Take `⟨-, g2, g3, -, h5, -⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W`. Establish `hfd : IsFundamentalDomain (GQ W) (stdDom (GQ W)) m` using `isFundamentalDomain_stdDom _ m`.

Establish `hfin` using `GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W m _ hm hfd`. Establish `hcnt : Countable (GQ W)` using `Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram`. Establish `hNc : Continuous N` using `(GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ W.rank W.rank N (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ W.rank W.rank N hN)).1`. Establish `hfm : Measurable fun h : GA D W => ‖N (ww W x₀ h)‖ₑ` using `(hNc.comp (continuous_ww x₀)).enorm.measurable`. Establish `hu : ∀ γ : GQ W, ∃ u : GL (Fin W.rank) D.host.E, mt W γ.1 = rat u.1` using `fun γ => by`.

Take `⟨u, -, hu⟩` from `γ.2`. Conclude with `⟨u, (congrArg Units.val hu).symm⟩`. Use `choose u hu using hu`. Establish `hxu : IsUnit x₀.det` using `isUnit_iff_ne_zero.2 hx`. Establish `hrk : ∀ γ : GQ W, ((u γ).1 * x₀).rank = W.rank` using `fun γ => by`.

Establish `h1 : IsUnit ((u γ).1 * x₀)`. Use `(Matrix.isUnit_iff_isUnit_det _).2 ?_` and prove the remaining obligations. Rewrite using `[Matrix.det_mul]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 (u γ).isUnit).mul hxu`. Simplify using `using Matrix.rank_of_isUnit _ h1`.

Set `e : GQ W → {x : Matrix (Fin W.rank) (Fin W.rank) D.host.E // x.rank = W.rank}` to `fun γ => ⟨(u γ).1 * x₀, hrk γ⟩`. Establish `he : Function.Injective e` using `fun γ γ' h => by`. Establish `h1 : (u γ).1 * x₀ = (u γ').1 * x₀` using `congrArg Subtype.val h`. Establish `h2 : (u γ).1 = (u γ').1`. Establish `hxi : x₀ * x₀⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hxu`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Subtype.ext (GlobalTheory.MixModel.mt_injective W (by rw [hu, hu, h2]))`. Establish `hterm : ∀ (γ : GQ W) (h : GA D W), ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ = ‖N (mm (mt W h⁻¹) (rat (e γ).1))‖ₑ` using `fun γ h => by`. Establish `h1 : (γ⁻¹ • h)⁻¹ = h⁻¹ * γ.1`. Express the relevant statement in the definitionally equal form `((γ.1)⁻¹ * h)⁻¹ = _`.

Rewrite using `[mul_inv_rev, inv_inv]`. Establish `h2 : mt W (h⁻¹ * γ.1) = mt W h⁻¹ * mt W γ.1` using `rfl`. Establish `h3 : ww W x₀ (γ⁻¹ • h) = mm (mt W h⁻¹) (rat (e γ).1)`. Simplify using `only [ww, e]`. Rewrite using `[h1, h2, hu, rat_mul]`.

Conclude with `Matrix.mul_assoc _ _ _`. Rewrite using `[h3]`. Rewrite using `[hfd.lintegral_eq_tsum']`. Rewrite using `[← lintegral_tsum fun γ => ?_]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hterm]`. Conclude with `(ENNReal.tsum_comp_le_tsum_of_injective he (fun x => ‖N (mm (mt W h⁻¹) (rat x.1))‖ₑ)).trans (hC h)`. Use `_ = C * m (stdDom (GQ W)) := by simp`. Use `_ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin`. Conclude with `(hfm.comp (measurable_const_smul γ⁻¹)).aemeasurable`.
-/
theorem orbFin_of_latBound : LatBound → OrbFin := by
  intro hL D θ hθ W m hm x₀ hx N hN
  obtain ⟨C, hC⟩ := hL D θ hθ W W.rank N hN
  have hB : BorelSpace (GA D W) := ⟨rfl⟩
  obtain ⟨-, g2, g3, -, h5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hfd : IsFundamentalDomain (GQ W) (stdDom (GQ W)) m := isFundamentalDomain_stdDom _ m
  have hfin := GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol W m _ hm hfd
  have hcnt : Countable (GQ W) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig W.gram
  have hNc : Continuous N :=
    (GlobalTheory.SchwartzMaj.continuous_and_le_maj D θ hθ W.rank W.rank N
      (GlobalTheory.SchwartzPure.isSchwartzBruhat_of_mem_schwartzA D θ hθ W.rank W.rank N hN)).1
  have hfm : Measurable fun h : GA D W => ‖N (ww W x₀ h)‖ₑ :=
    (hNc.comp (continuous_ww x₀)).enorm.measurable

  classical
  have hu : ∀ γ : GQ W, ∃ u : GL (Fin W.rank) D.host.E, mt W γ.1 = rat u.1 := fun γ => by
    obtain ⟨u, -, hu⟩ := γ.2
    exact ⟨u, (congrArg Units.val hu).symm⟩
  choose u hu using hu
  have hxu : IsUnit x₀.det := isUnit_iff_ne_zero.2 hx
  have hrk : ∀ γ : GQ W, ((u γ).1 * x₀).rank = W.rank := fun γ => by
    have h1 : IsUnit ((u γ).1 * x₀) := by
      refine (Matrix.isUnit_iff_isUnit_det _).2 ?_
      rw [Matrix.det_mul]
      exact ((Matrix.isUnit_iff_isUnit_det _).1 (u γ).isUnit).mul hxu
    simpa using Matrix.rank_of_isUnit _ h1
  let e : GQ W → {x : Matrix (Fin W.rank) (Fin W.rank) D.host.E // x.rank = W.rank} :=
    fun γ => ⟨(u γ).1 * x₀, hrk γ⟩
  have he : Function.Injective e := fun γ γ' h => by
    have h1 : (u γ).1 * x₀ = (u γ').1 * x₀ := congrArg Subtype.val h
    have h2 : (u γ).1 = (u γ').1 := by
      have hxi : x₀ * x₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hxu
      calc (u γ).1 = (u γ).1 * x₀ * x₀⁻¹ := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
        _ = (u γ').1 * x₀ * x₀⁻¹ := by rw [h1]
        _ = (u γ').1 := by rw [Matrix.mul_assoc, hxi, Matrix.mul_one]
    exact Subtype.ext (GlobalTheory.MixModel.mt_injective W (by rw [hu, hu, h2]))
  have hterm : ∀ (γ : GQ W) (h : GA D W), ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ = ‖N (mm (mt W h⁻¹) (rat (e γ).1))‖ₑ := fun γ h => by
    have h1 : (γ⁻¹ • h)⁻¹ = h⁻¹ * γ.1 := by
      change ((γ.1)⁻¹ * h)⁻¹ = _
      rw [mul_inv_rev, inv_inv]
    have h2 : mt W (h⁻¹ * γ.1) = mt W h⁻¹ * mt W γ.1 := rfl
    have h3 : ww W x₀ (γ⁻¹ • h) = mm (mt W h⁻¹) (rat (e γ).1) := by
      simp only [ww, e]
      rw [h1, h2, hu, rat_mul]
      exact Matrix.mul_assoc _ _ _
    rw [h3]
  rw [hfd.lintegral_eq_tsum']
  rw [← lintegral_tsum fun γ => ?_]
  · calc ∫⁻ h in stdDom (GQ W), ∑' γ : GQ W, ‖N (ww W x₀ (γ⁻¹ • h))‖ₑ ∂m
        ≤ ∫⁻ _ in stdDom (GQ W), (C : ℝ≥0∞) ∂m := lintegral_mono fun h => by
          simp only [hterm]
          exact (ENNReal.tsum_comp_le_tsum_of_injective he
            (fun x => ‖N (mm (mt W h⁻¹) (rat x.1))‖ₑ)).trans (hC h)
      _ = C * m (stdDom (GQ W)) := by simp
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.coe_lt_top hfin
  · exact (hfm.comp (measurable_const_smul γ⁻¹)).aemeasurable

end GlobalTheory.CompanionTheory.ColumnSplitting
end
