import Development.WeilBound.ThetaLifts.LatticeBasics.Hypotheses2
import Development.WeilBound.ThetaLifts.LatticeBasics.SliceSeminorm
import GroundTheory.GlobalFields.TateThesis.AdeleScaling

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global
open GlobalTheory.Doubling (absE)

attribute [local instance 100000] measurableSpace_adeleRing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {m n : ℕ}

/- English proof (translation)
Take `⟨s, hs, h0⟩` from `exists_compact_mem_nhds (0 : AF F)`. Use `Measure.regular_of_isAddLeftInvariant (μ := adeleMeasure F) hs ⟨0, mem_interior_iff_mem_nhds.2 h0⟩ hs.measure_lt_top.ne` as an intermediate fact. Use `distribHaarChar_eq_of_measure_smul_eq_mul (μ := adeleMeasure F) (g := a) (r := ⟨IdeleGroup.ideleModule F a, (IdeleGroup.ideleModule F a).2.le⟩) (Measure.measure_pos_of_mem_nhds _ h0).ne' hs.measure_lt_top.ne ((adeleMeasure_smul a s).trans (congrArg (· * _) (ENNReal.ofReal_eq_coe_ …` as an intermediate fact. Conclude with `congrArg NNReal.toReal this`.
-/
theorem modu_eq (a : (AF F)ˣ) : ((adeleClass F).modu a : ℝ) = IdeleGroup.ideleModule F a := by
  obtain ⟨s, hs, h0⟩ := exists_compact_mem_nhds (0 : AF F)
  have := Measure.regular_of_isAddLeftInvariant (μ := adeleMeasure F) hs ⟨0, mem_interior_iff_mem_nhds.2 h0⟩
    hs.measure_lt_top.ne
  have := distribHaarChar_eq_of_measure_smul_eq_mul (μ := adeleMeasure F) (g := a)
    (r := ⟨IdeleGroup.ideleModule F a, (IdeleGroup.ideleModule F a).2.le⟩) (Measure.measure_pos_of_mem_nhds _ h0).ne'
    hs.measure_lt_top.ne ((adeleMeasure_smul a s).trans (congrArg (· * _) (ENNReal.ofReal_eq_coe_nnreal _)))
  exact congrArg NNReal.toReal this

/- English proof (translation)
Rewrite using `[modu_eq, IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply]`. Simplify using `only [GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]`. Rewrite using `[NNReal.coe_mul, NNReal.coe_prod]`. Conclude with `congrArg₂ _ rfl (coe_finprod_nnnorm (IdeleGroup.toFinite F (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x))).symm`.
-/
theorem modu_norm (x : (AE F E)ˣ) :
    ((adeleClass F).modu (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x) : ℝ) = absE F E x := by
  rw [modu_eq, IdeleGroup.ideleModule_eq, GlobalTheory.Doubling.absE_apply]
  simp only [GlobalTheory.Doubling.absEv_unitFin, GlobalTheory.Doubling.absEw_unitInf]
  rw [NNReal.coe_mul, NNReal.coe_prod]
  exact congrArg₂ _ rfl (coe_finprod_nnnorm
    (IdeleGroup.toFinite F (Units.map (Algebra.norm (AF F) : AE F E →* AF F) x))).symm

/- English proof (translation)
Use `⟨h.weil.2.1.cont l h.adm Φ hΦ, fun p t x hp => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, Module.End.mul_apply, h.weil.2.2 l h.adm h.kill p t hp _ (h.weil.2.1.pres x Φ hΦ), modu_norm, Complex.ofReal_cpow (NNReal.coe_nonneg _)]`. Use `congr 3`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sec_cont_law {Y : Spc F E n} {A : Spc F E m} {ψ : AddChar (AF F) ℂ} {κ : Type} [Fintype κ] {dd} {χ : Chr F E} {om S l}
    (h : IsDbl (σ := σ) (A := A) (Y := Y) (κ := κ) ψ dd χ om S l) {Φ} (hΦ : Φ ∈ schA F κ) :
    (Continuous fun x => l (om x Φ)) ∧ ∀ p t x, IsPar p t → l (om (p * x) Φ) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
      ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ (((m : ℂ) - n) / 2 + n / 2) * l (om x Φ) := by
  refine ⟨h.weil.2.1.cont l h.adm Φ hΦ, fun p t x hp => ?_⟩
  rw [map_mul, Module.End.mul_apply, h.weil.2.2 l h.adm h.kill p t hp _ (h.weil.2.1.pres x Φ hΦ), modu_norm,
    Complex.ofReal_cpow (NNReal.coe_nonneg _)]
  congr 3
  simp; ring

end GlobalTheory.ThK.Dbl

end
