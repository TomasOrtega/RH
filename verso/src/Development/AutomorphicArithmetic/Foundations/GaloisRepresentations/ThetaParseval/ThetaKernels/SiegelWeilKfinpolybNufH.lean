import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.IntegralJnp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfpDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfinpolybNuf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockIntSch

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFPB
open PositivityTheory.SiegelWeilFormula.KFP
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
/- English proof (translation)
Take `⟨i1, i2, i3, i4⟩` from `(PositivityTheory.ThKCT.ideleTop F E).1`. Use `haveI : BorelSpace (AE F E) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))`. Use `haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Use `haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace`. Use `haveI : MeasurableAdd (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := inferInstance`. Use `haveI : SigmaFinite νf := inferInstance`. Use `haveI : ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _`.

Conclude with `ContinuousAddEquiv.isAddHaarMeasure_map ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf) (_root_.PositivityTheory.SiegelWeilFormula.KFPB.jnpE_k R)`.
-/
theorem map_isHaar_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) [νf.IsAddHaarMeasure] :
    (Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)).IsAddHaarMeasure := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  haveI : MeasurableAdd (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := inferInstance
  haveI : SigmaFinite νf := inferInstance
  haveI : ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact ContinuousAddEquiv.isAddHaarMeasure_map ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf) (_root_.PositivityTheory.SiegelWeilFormula.KFPB.jnpE_k R)
/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Conclude with `⟨Measure.addHaar, inferInstance, _root_.PositivityTheory.SiegelWeilFormula.KFPB.map_isHaar_k R _⟩`.
-/
theorem exists_nuf'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : ∃ νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d), νf.IsAddHaarMeasure ∧
    (Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)).IsAddHaarMeasure := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  exact ⟨Measure.addHaar, inferInstance, _root_.PositivityTheory.SiegelWeilFormula.KFPB.map_isHaar_k R _⟩
/- English proof (translation)
Take `⟨i1, i2, i3, i4⟩` from `(PositivityTheory.ThKCT.ideleTop F E).1`. Use `haveI : BorelSpace (AE F E) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))`. Use `haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Use `haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace`. Use `haveI : SigmaFinite νf := inferInstance`. Use `set μ := (volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf with hμ`. Set `e : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d ≃ᵐ Mx F E d.m d.n` to `(_root_.PositivityTheory.SiegelWeilFormula.KFPB.jnpE_k R).toHomeomorph.toMeasurableEquiv`.

Establish `hmap : Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) μ = Measure.map e μ` using `rfl`. Establish `hH : (Measure.map e μ).IsAddHaarMeasure` using `_root_.PositivityTheory.SiegelWeilFormula.KFPB.map_isHaar_k R νf`. Establish `hfi : Integrable (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2)) μ` using `(integrable_map_equiv e f).1 (_root_.PositivityTheory.SiegelWeilFormula.KFock.int_schM_k d _ hH hf)`. Take `⟨C, hC⟩` from `hg'.1.continuous.bounded_above_of_compact_support hg'.2`. Establish `hint : Integrable (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) * star (b p.1 * g p.2)) μ`.

Use `hfi.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Conclude with `(continuous_star.comp ((hb.comp continuous_fst).mul (hg'.1.continuous.comp continuous_snd))).aestronglyMeasurable`. Rewrite using `[norm_star, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hmap, integral_map_equiv]`.

Establish `he : ∀ p, e p = _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2` using `fun p => rfl`. Simplify using `only [he, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k]`. Rewrite using `[integral_prod _ hint]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [_root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k, star_mul]`.

Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_jnp'_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {νf : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) {g : _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d → ℂ} (hg' : g ∈ SB (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d)) {b : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d → ℂ} (hb : Continuous b) (hb1 : ∀ u, ‖b u‖ ≤ 1) :
    ∫ X, f X * star (b (_root_.PositivityTheory.SiegelWeilFormula.KFP.arc_k R X) * g (_root_.PositivityTheory.SiegelWeilFormula.KFP.fin_k d X))
        ∂(Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) ((volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf)) =
      ∫ u, star (b u) * _root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k R νf f g u := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (_root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d) := Pi.borelSpace
  haveI : SigmaFinite νf := inferInstance
  set μ := (volume : Measure (_root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d)).prod νf with hμ
  let e : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d ≃ᵐ Mx F E d.m d.n := (_root_.PositivityTheory.SiegelWeilFormula.KFPB.jnpE_k R).toHomeomorph.toMeasurableEquiv
  have hmap : Measure.map (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) μ = Measure.map e μ := rfl
  have hH : (Measure.map e μ).IsAddHaarMeasure := _root_.PositivityTheory.SiegelWeilFormula.KFPB.map_isHaar_k R νf
  have hfi : Integrable (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2)) μ :=
    (integrable_map_equiv e f).1 (_root_.PositivityTheory.SiegelWeilFormula.KFock.int_schM_k d _ hH hf)
  obtain ⟨C, hC⟩ := hg'.1.continuous.bounded_above_of_compact_support hg'.2
  have hint : Integrable (fun p : _root_.PositivityTheory.SiegelWeilFormula.KFP.Vw_k d × _root_.PositivityTheory.SiegelWeilFormula.KFP.Yf_k d => f (_root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2) * star (b p.1 * g p.2)) μ := by
    refine hfi.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (continuous_star.comp ((hb.comp continuous_fst).mul (hg'.1.continuous.comp continuous_snd))).aestronglyMeasurable
    · rw [norm_star, norm_mul]
      calc ‖b p.1‖ * ‖g p.2‖ ≤ 1 * C := mul_le_mul (hb1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
  rw [hmap, integral_map_equiv]
  have he : ∀ p, e p = _root_.PositivityTheory.SiegelWeilFormula.KFP.jn_k R p.1 p.2 := fun p => rfl
  simp only [he, _root_.PositivityTheory.SiegelWeilFormula.KFP.arc_jn_k, _root_.PositivityTheory.SiegelWeilFormula.KFP.fin_jn_k]
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [_root_.PositivityTheory.SiegelWeilFormula.KFP.hg_k, star_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring
end PositivityTheory.SiegelWeilFormula.KFPB
end
end
