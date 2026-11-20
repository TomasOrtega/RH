import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.RatVecCountable
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.ContinuousPhz

set_option linter.style.haveILetI false

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act

open ComplexParameterFamilyContinuity

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d`. Use `⟨fun nb lam 𝓖 h => ?_, fun L uM ν 𝓤 h => ?_⟩` and prove the remaining obligations. Establish `hσ` using `kfour.sigma_sigma_of_good d.ok.good`. Take `⟨hlc, hsc, ht2, hbo⟩` from `kfour.nA_top hσ d.ok.frame`. Take `⟨K, hK, hc⟩` from `kfour.nF_cocompact hσ d.ok.frame`.

Take `⟨hnb, hlam, hfd, h1⟩` from `h`. Take `⟨𝓖₀, hfd₀, hcpt⟩` from `addFD_of_cover' (nF σ d.Y d.b) hK hc lam`. Conclude with `⟨𝓖₀, ⟨hnb, hlam, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩`. Take `⟨hfr, hν, hfd, h1⟩` from `h haveI : DiscreteTopology L.ratV := ratVec_discrete (F := F) (E := E) L.n haveI : Countable L.ratV := ratVec_countable (F := F) (E := E) L.n`. Take `⟨K, hK, hc⟩ : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ v, ∃ γ ∈ L.ratV, γ + v ∈ K` from `ratVec_cocompact (F := F) (E := E) L.n`.

Take `⟨𝓤₀, hfd₀, hcpt⟩` from `addFD_of_cover' L.ratV hK hc ν`. Conclude with `⟨𝓤₀, ⟨hfr, hν, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩`.
-/
theorem cptDom : CptDom := by
  intro F E _ _ _ _ _ σ d
  refine ⟨fun nb lam 𝓖 h => ?_, fun L uM ν 𝓤 h => ?_⟩
  · have hσ := kfour.sigma_sigma_of_good d.ok.good
    obtain ⟨hlc, hsc, ht2, hbo⟩ := kfour.nA_top hσ d.ok.frame
    obtain ⟨K, hK, hc⟩ := kfour.nF_cocompact hσ d.ok.frame
    obtain ⟨hnb, hlam, hfd, h1⟩ := h
    obtain ⟨𝓖₀, hfd₀, hcpt⟩ := addFD_of_cover' (nF σ d.Y d.b) hK hc lam
    exact ⟨𝓖₀, ⟨hnb, hlam, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩
  · obtain ⟨hfr, hν, hfd, h1⟩ := h
    haveI : DiscreteTopology L.ratV := ratVec_discrete (F := F) (E := E) L.n
    haveI : Countable L.ratV := ratVec_countable (F := F) (E := E) L.n
    obtain ⟨K, hK, hc⟩ : ∃ K : Set (Fin L.n → AE F E), IsCompact K ∧ ∀ v, ∃ γ ∈ L.ratV, γ + v ∈ K :=
      ratVec_cocompact (F := F) (E := E) L.n
    obtain ⟨𝓤₀, hfd₀, hcpt⟩ := addFD_of_cover' L.ratV hK hc ν
    exact ⟨𝓤₀, ⟨hfr, hν, hfd₀, by rw [← h1]; exact hfd₀.measure_eq hfd⟩, hcpt⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d L s₁ f hf he`. Take `⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩` from `he 0`. Use `⟨t, fun z hz nb lam 𝓖 h𝓖 hc𝓖 uM ν 𝓤 h𝓤 hc𝓤 T x => ?_⟩` and prove the remaining obligations. Take `⟨hTG, -⟩` from `kfour.doubled_group_topological_properties σ d.Y`. Establish `hσ` using `kfour.sigma_sigma_of_good d.ok.good`.

Take `⟨iLC, iSC, iT2, iBo⟩` from `kfour.nA_top hσ d.ok.frame`. Take `⟨hnb, hlam, hfd, h1⟩` from `h𝓖`. Take `⟨hfr, hν, hfdU, hU1⟩` from `h𝓤`. Establish `cu : Continuous uM` using `continuous_uM L ⟨hfr, hν, hfdU, hU1⟩`. Establish `cn : Continuous nb` using `kunf.continuous_nb hnb`.

Establish `cφ : Continuous (phz d f s₁ z)` using `continuous_phz d hf.cont s₁ z`. Use `set m : (Fin L.n → AE F E) × nA σ d.Y d.b → d.G := fun p => nb p.2 * (uM p.1 * x) with hm`. Establish `cm : Continuous m` using `(cn.comp continuous_snd).mul ((cu.comp continuous_fst).mul continuous_const)`. Establish `hKc : IsCompact (closure 𝓤 ×ˢ closure 𝓖)` using `hc𝓤.prod hc𝓖`. Take `⟨u, hu, hub⟩` from `(hmaj z hz).1 (m '' (closure 𝓤 ×ˢ closure 𝓖)) (hKc.image cm)`.

Establish `hψ` using `GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std`. Establish `cψ` using `kfour.continuous_chr (σ := σ) (Y := d.Y) (b := d.b) hψ.1 T.1.1`. Take `⟨Mψ, hMψ⟩` from `hc𝓖.exists_bound_of_continuousOn cψ.continuousOn`. Use `set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ`. Use `haveI : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by rw [hU1]; exact ENNReal.one_ne_top)`.

Use `haveI : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)`. Establish `hS : ∀ᵐ p ∂μ, p ∈ closure 𝓤 ×ˢ closure 𝓖`. Rewrite using `[ae_iff]`. Use `measure_mono_null (t := (closure 𝓤)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (closure 𝓖)ᶜ) ?_ ?_` and prove the remaining obligations. Introduce `p hp`.

Simplify using `only [Set.mem_ofPred_eq, Set.mem_prod, not_and_or] at hp`. Break down `hp with hp | hp` into its components or cases. Conclude with `Or.inl ⟨hp, Set.mem_univ _⟩`. Conclude with `Or.inr ⟨Set.mem_univ _, hp⟩`. Establish `eU : (closure 𝓤)ᶜ ∩ 𝓤 = ∅` using `(show Disjoint (closure 𝓤)ᶜ 𝓤 from Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓤)ᶜ) (h' : y ∈ 𝓤) => hy (subset_closure h')).inter_eq`.

Establish `eG : (closure 𝓖)ᶜ ∩ 𝓖 = ∅` using `(show Disjoint (closure 𝓖)ᶜ 𝓖 from Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓖)ᶜ) (h' : y ∈ 𝓖) => hy (subset_closure h')).inter_eq`. Use `measure_union_null ?_ ?_` and prove the remaining obligations. Rewrite using `[Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eU, measure_empty, zero_mul]`. Rewrite using `[Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eG, measure_empty, mul_zero]`. Establish `hbd : ∀ q : Cs d, ∀ᵐ p ∂μ, ‖kq L f s₁ z nb T uM (rep q) x p‖ ≤ |u q| * |Mψ|`.

Introduce `q`. Use `filter_upwards [hS] with p hp`. Simplify using `only [kq, norm_mul]`. Use `mul_le_mul ((hub (m p) ⟨p, hp, rfl⟩ q).trans (le_abs_self _)) ((hMψ p.2 hp.2).trans (le_abs_self _)) (norm_nonneg _) (abs_nonneg _)` and prove the remaining obligations. Establish `hcq : ∀ q : Cs d, Continuous (kq L f s₁ z nb T uM (rep q) x)` using `fun q => (cφ.comp (continuous_const.mul cm)).mul (cψ.comp continuous_snd)`.

Establish `hint : ∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) μ` using `fun q => Integrable.of_bound (hcq q).aestronglyMeasurable _ (hbd q)`. Use `⟨hint, ?_⟩` and prove the remaining obligations. Use `Summable.of_nonneg_of_le (fun q => integral_nonneg fun p => norm_nonneg _) (fun q => ?_) ((hu.abs.mul_right |Mψ|).mul_right (μ.real Set.univ))` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem absConv : AbsConv := by
  intro F E _ _ _ _ _ σ d L s₁ f hf he
  obtain ⟨U, p, Ê, t, -, -, -, -, -, -, -, hmaj⟩ := he 0
  refine ⟨t, fun z hz nb lam 𝓖 h𝓖 hc𝓖 uM ν 𝓤 h𝓤 hc𝓤 T x => ?_⟩
  obtain ⟨hTG, -⟩ := kfour.doubled_group_topological_properties σ d.Y
  have hσ := kfour.sigma_sigma_of_good d.ok.good
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top hσ d.ok.frame
  obtain ⟨hnb, hlam, hfd, h1⟩ := h𝓖
  obtain ⟨hfr, hν, hfdU, hU1⟩ := h𝓤
  have cu : Continuous uM := continuous_uM L ⟨hfr, hν, hfdU, hU1⟩
  have cn : Continuous nb := kunf.continuous_nb hnb
  have cφ : Continuous (phz d f s₁ z) := continuous_phz d hf.cont s₁ z
  set m : (Fin L.n → AE F E) × nA σ d.Y d.b → d.G := fun p => nb p.2 * (uM p.1 * x) with hm
  have cm : Continuous m := (cn.comp continuous_snd).mul ((cu.comp continuous_fst).mul continuous_const)
  have hKc : IsCompact (closure 𝓤 ×ˢ closure 𝓖) := hc𝓤.prod hc𝓖
  obtain ⟨u, hu, hub⟩ := (hmaj z hz).1 (m '' (closure 𝓤 ×ˢ closure 𝓖)) (hKc.image cm)
  have hψ := GlobalTheory.StdCharWeilDatum.isCharAF d.ok.good.std
  have cψ := kfour.continuous_chr (σ := σ) (Y := d.Y) (b := d.b) hψ.1 T.1.1
  obtain ⟨Mψ, hMψ⟩ := hc𝓖.exists_bound_of_continuousOn cψ.continuousOn
  set μ := (ν.restrict 𝓤).prod (lam.restrict 𝓖) with hμ
  haveI : IsFiniteMeasure (ν.restrict 𝓤) := isFiniteMeasure_restrict.2 (by rw [hU1]; exact ENNReal.one_ne_top)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) := isFiniteMeasure_restrict.2 (by rw [h1]; exact ENNReal.one_ne_top)
  have hS : ∀ᵐ p ∂μ, p ∈ closure 𝓤 ×ˢ closure 𝓖 := by
    rw [ae_iff]
    refine measure_mono_null (t := (closure 𝓤)ᶜ ×ˢ Set.univ ∪ Set.univ ×ˢ (closure 𝓖)ᶜ) ?_ ?_
    · intro p hp
      simp only [Set.mem_ofPred_eq, Set.mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · exact Or.inl ⟨hp, Set.mem_univ _⟩
      · exact Or.inr ⟨Set.mem_univ _, hp⟩
    · have eU : (closure 𝓤)ᶜ ∩ 𝓤 = ∅ := (show Disjoint (closure 𝓤)ᶜ 𝓤 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓤)ᶜ) (h' : y ∈ 𝓤) => hy (subset_closure h')).inter_eq
      have eG : (closure 𝓖)ᶜ ∩ 𝓖 = ∅ := (show Disjoint (closure 𝓖)ᶜ 𝓖 from
        Set.disjoint_left.2 fun y (hy : y ∈ (closure 𝓖)ᶜ) (h' : y ∈ 𝓖) => hy (subset_closure h')).inter_eq
      refine measure_union_null ?_ ?_
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eU, measure_empty, zero_mul]
      · rw [Measure.prod_prod, Measure.restrict_apply isClosed_closure.measurableSet.compl, eG, measure_empty, mul_zero]
  have hbd : ∀ q : Cs d, ∀ᵐ p ∂μ, ‖kq L f s₁ z nb T uM (rep q) x p‖ ≤ |u q| * |Mψ| := by
    intro q
    filter_upwards [hS] with p hp
    simp only [kq, norm_mul]
    refine mul_le_mul ((hub (m p) ⟨p, hp, rfl⟩ q).trans (le_abs_self _)) ((hMψ p.2 hp.2).trans (le_abs_self _))
      (norm_nonneg _) (abs_nonneg _)
  have hcq : ∀ q : Cs d, Continuous (kq L f s₁ z nb T uM (rep q) x) := fun q =>
    (cφ.comp (continuous_const.mul cm)).mul (cψ.comp continuous_snd)
  have hint : ∀ q : Cs d, Integrable (kq L f s₁ z nb T uM (rep q) x) μ := fun q =>
    Integrable.of_bound (hcq q).aestronglyMeasurable _ (hbd q)
  refine ⟨hint, ?_⟩
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun p => norm_nonneg _) (fun q => ?_)
    ((hu.abs.mul_right |Mψ|).mul_right (μ.real Set.univ))
  calc ∫ p, ‖kq L f s₁ z nb T uM (rep q) x p‖ ∂μ ≤ ∫ _p, |u q| * |Mψ| ∂μ :=
        integral_mono_ae (hint q).norm (integrable_const _) (hbd q)
    _ = |u q| * |Mψ| * μ.real Set.univ := by rw [integral_const, smul_eq_mul, mul_comm]

end PositivityTheory.SiegelWeilFormula.Act

end
