import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.PolynomialGaussianIntegrals.ContinuousLoc

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical InnerProductSpace
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KFPB

open PositivityTheory.SiegelWeilFormula.KFP

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ}

/- English proof (translation)
Take `⟨i1, i2, i3, i4⟩` from `(PositivityTheory.ThKCT.ideleTop F E).1`. Use `haveI : BorelSpace (AE F E) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))`. Use `haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Use `haveI : BorelSpace (Yf d) := Pi.borelSpace`. Use `haveI : MeasurableAdd (Yf d) := inferInstance`. Use `haveI : SigmaFinite νf := inferInstance`. Use `haveI : ((volume : Measure (Vw d)).prod νf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _`.

Conclude with `ContinuousAddEquiv.isAddHaarMeasure_map ((volume : Measure (Vw d)).prod νf) (jnpE R)`.
-/
theorem map_isHaar (R : RD d) (νf : Measure (Yf d)) [νf.IsAddHaarMeasure] :
    (Measure.map (fun p : Vw d × Yf d => jn R p.1 p.2) ((volume : Measure (Vw d)).prod νf)).IsAddHaarMeasure := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (Yf d) := Pi.borelSpace
  haveI : MeasurableAdd (Yf d) := inferInstance
  haveI : SigmaFinite νf := inferInstance
  haveI : ((volume : Measure (Vw d)).prod νf).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  exact ContinuousAddEquiv.isAddHaarMeasure_map ((volume : Measure (Vw d)).prod νf) (jnpE R)

/- English proof (translation)
Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`. Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Conclude with `⟨Measure.addHaar, inferInstance, map_isHaar R _⟩`.
-/
theorem exists_nuf' (R : RD d) : ∃ νf : Measure (Yf d), νf.IsAddHaarMeasure ∧
    (Measure.map (fun p : Vw d × Yf d => jn R p.1 p.2) ((volume : Measure (Vw d)).prod νf)).IsAddHaarMeasure := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  exact ⟨Measure.addHaar, inferInstance, map_isHaar R _⟩

/- English proof (translation)
Take `⟨i1, i2, i3, i4⟩` from `(PositivityTheory.ThKCT.ideleTop F E).1`. Use `haveI : BorelSpace (AE F E) := ⟨rfl⟩`. Use `haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))`. Use `haveI : IsTopologicalAddGroup (Mx F E d.m d.n) := inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))`. Use `haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F`.

Use `haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F`. Use `haveI : BorelSpace (Yf d) := Pi.borelSpace`. Use `haveI : SigmaFinite νf := inferInstance`. Use `set μ := (volume : Measure (Vw d)).prod νf with hμ`. Set `e : Vw d × Yf d ≃ᵐ Mx F E d.m d.n` to `(jnpE R).toHomeomorph.toMeasurableEquiv`.

Establish `hmap : Measure.map (fun p : Vw d × Yf d => jn R p.1 p.2) μ = Measure.map e μ` using `rfl`. Establish `hH : (Measure.map e μ).IsAddHaarMeasure` using `map_isHaar R νf`. Establish `hfi : Integrable (fun p : Vw d × Yf d => f (jn R p.1 p.2)) μ` using `(integrable_map_equiv e f).1 (KFock.int_schM d _ hH hf)`. Take `⟨C, hC⟩` from `hg'.1.continuous.bounded_above_of_compact_support hg'.2`. Establish `hint : Integrable (fun p : Vw d × Yf d => f (jn R p.1 p.2) * star (b p.1 * g p.2)) μ`.

Use `hfi.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Conclude with `(continuous_star.comp ((hb.comp continuous_fst).mul (hg'.1.continuous.comp continuous_snd))).aestronglyMeasurable`. Rewrite using `[norm_star, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hmap, integral_map_equiv]`.

Establish `he : ∀ p, e p = jn R p.1 p.2` using `fun p => rfl`. Simplify using `only [he, arc_jn, fin_jn]`. Rewrite using `[integral_prod _ hint]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Simplify using `only [hg, star_mul]`.

Rewrite using `[← integral_const_mul]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_jnp' (R : RD d) {νf : Measure (Yf d)} (hνf : νf.IsAddHaarMeasure) {f : Mx F E d.m d.n → ℂ}
    (hf : f ∈ d.schM) {g : Yf d → ℂ} (hg' : g ∈ SB (Yf d)) {b : Vw d → ℂ} (hb : Continuous b) (hb1 : ∀ u, ‖b u‖ ≤ 1) :
    ∫ X, f X * star (b (arc R X) * g (fin d X))
        ∂(Measure.map (fun p : Vw d × Yf d => jn R p.1 p.2) ((volume : Measure (Vw d)).prod νf)) =
      ∫ u, star (b u) * hg R νf f g u := by
  obtain ⟨i1, i2, i3, i4⟩ := (PositivityTheory.ThKCT.ideleTop F E).1
  haveI : BorelSpace (AE F E) := ⟨rfl⟩
  haveI : BorelSpace (Mx F E d.m d.n) := inferInstanceAs (BorelSpace (Fin d.m → Fin d.n → AE F E))
  haveI : IsTopologicalAddGroup (Mx F E d.m d.n) :=
    inferInstanceAs (IsTopologicalAddGroup (Fin d.m → Fin d.n → AE F E))
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : BorelSpace (Yf d) := Pi.borelSpace
  haveI : SigmaFinite νf := inferInstance
  set μ := (volume : Measure (Vw d)).prod νf with hμ
  let e : Vw d × Yf d ≃ᵐ Mx F E d.m d.n := (jnpE R).toHomeomorph.toMeasurableEquiv
  have hmap : Measure.map (fun p : Vw d × Yf d => jn R p.1 p.2) μ = Measure.map e μ := rfl
  have hH : (Measure.map e μ).IsAddHaarMeasure := map_isHaar R νf
  have hfi : Integrable (fun p : Vw d × Yf d => f (jn R p.1 p.2)) μ :=
    (integrable_map_equiv e f).1 (KFock.int_schM d _ hH hf)
  obtain ⟨C, hC⟩ := hg'.1.continuous.bounded_above_of_compact_support hg'.2
  have hint : Integrable (fun p : Vw d × Yf d => f (jn R p.1 p.2) * star (b p.1 * g p.2)) μ := by
    refine hfi.mul_bdd (c := C) ?_ (Filter.Eventually.of_forall fun p => ?_)
    · exact (continuous_star.comp ((hb.comp continuous_fst).mul (hg'.1.continuous.comp continuous_snd))).aestronglyMeasurable
    · rw [norm_star, norm_mul]
      calc ‖b p.1‖ * ‖g p.2‖ ≤ 1 * C := mul_le_mul (hb1 _) (hC _) (norm_nonneg _) zero_le_one
        _ = C := one_mul C
  rw [hmap, integral_map_equiv]
  have he : ∀ p, e p = jn R p.1 p.2 := fun p => rfl
  simp only [he, arc_jn, fin_jn]
  rw [integral_prod _ hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  simp only [hg, star_mul]
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

end PositivityTheory.SiegelWeilFormula.KFPB

end
