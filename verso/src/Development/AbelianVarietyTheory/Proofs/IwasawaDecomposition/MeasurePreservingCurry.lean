import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockOrderedSumEquivTrueIndex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingGlueLowerUnitriangularBlocksStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralFlagDensityFibreBoundedDomainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LeadingMinorSignsOverBoundedFlagDomainStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LintegralPiFibreMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingFlagFibreChartCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DomainPointStabilizerTrivialStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFundamentalSetChartPreimageFundamentalDomainStatement

open Matrix NumberField MeasureTheory Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.HodgeDomain GlobalTheory.TrueCx GlobalTheory.FlagFibre
open scoped ComplexOrder ENNReal

noncomputable section

namespace GlobalTheory.FlagFibre

/- English proof (translation)
Establish `h : (volume : Measure (ι × κ → ℂ)) = (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]`. Establish `e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j)))`. Use extensionality with `f`.

Simplify using `[MeasurableEquiv.coe_curry_symm, Function.uncurry]`. Rewrite using `[e, volume_pi, Measure.pi_pi]`. Repeatedly rewrite using `[volume_pi, Measure.pi_pi]`. Rewrite using `[Fintype.prod_prod_type]`. Use `⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩` and prove the remaining obligations.

Rewrite using `[h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]`. Simplify using the standard rewrite rules.
-/
theorem measurePreserving_curry (ι κ : Type) [Fintype ι] [Fintype κ] :
    MeasurePreserving (MeasurableEquiv.curry ι κ ℂ) volume volume := by
  have h : (volume : Measure (ι × κ → ℂ)) =
      (volume : Measure (ι → κ → ℂ)).map (MeasurableEquiv.curry ι κ ℂ).symm := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply (MeasurableEquiv.measurable _) (MeasurableSet.univ_pi hs)]
    have e : (MeasurableEquiv.curry ι κ ℂ).symm ⁻¹' Set.univ.pi s =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
      ext f; simp [MeasurableEquiv.coe_curry_symm, Function.uncurry]
    rw [e, volume_pi, Measure.pi_pi]
    simp_rw [volume_pi, Measure.pi_pi]
    rw [Fintype.prod_prod_type]
  refine ⟨(MeasurableEquiv.curry ι κ ℂ).measurable, ?_⟩
  rw [h, Measure.map_map (MeasurableEquiv.measurable _) (MeasurableEquiv.measurable _)]
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r j : ℕ} (X : Data E r) (hj : j ≤ r) {Tau : Type}
  [Fintype Tau] (κ : Tau ≃ X.Ψ)

/- English proof (translation)
Introduce `τ`. Take `⟨t, rfl⟩` from `κ.surjective τ`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations. Establish `e : mat (cpt X (x0F X) z) (κ t) = mat (x0F X) (κ t) * uni (coords X κ z t)` using `rfl`. Rewrite using `[e, det_mul, det_uni, mul_one]`.

Conclude with `det_x0F X _`. Rewrite using `[dmin_cpt X κ z t i, hp]`. Use `GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) _ (reindex_sgn hj) _ ?_ i` and prove the remaining obligations. Establish `h` using `hz t`. Establish `e : unflat (proj X hj κ z) t = toMat (base (idx hj) (coords X κ z t))`.

Use extensionality with `a b`. Conclude with `proj_eq X hj κ z t (a, b)`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem mem_OmF_of_proj (hp : X.p0 = r - j) {z : V (nd X)} (hz : proj X hj κ z ∈ DomFlat Tau j (r - j)) :
    z ∈ OmF X (x0F X) := by
  intro τ
  obtain ⟨t, rfl⟩ := κ.surjective τ
  refine ⟨?_, fun i => ?_⟩
  · have e : mat (cpt X (x0F X) z) (κ t) = mat (x0F X) (κ t) * uni (coords X κ z t) := rfl
    rw [e, det_mul, det_uni, mul_one]
    exact det_x0F X _
  · rw [dmin_cpt X κ z t i, hp]
    refine GlobalTheory.T.leading_minor_signs_over_bounded_flag_domain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) _ (reindex_sgn hj) _ ?_ i
    have h := hz t
    have e : unflat (proj X hj κ z) t = toMat (base (idx hj) (coords X κ z t)) := by
      ext a b; exact proj_eq X hj κ z t (a, b)
    rwa [e] at h

/- English proof (translation)
The claim follows from `Set.inter_eq_left.2 fun _ hz => mem_OmF_of_proj X hj κ hp (hD hz)`.
-/
theorem inter_OmF (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hD : S ⊆ DomFlat Tau j (r - j)) :
    proj X hj κ ⁻¹' S ∩ OmF X (x0F X) = proj X hj κ ⁻¹' S :=
  Set.inter_eq_left.2 fun _ hz => mem_OmF_of_proj X hj κ hp (hD hz)

/- English proof (translation)
Rewrite using `[densF, ← κ.prod_comp]`. Conclude with `Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i _ => by rw [dmin_cpt X κ z t]`.
-/
theorem densF_eq (z : V (nd X)) :
    densF X (x0F X) z = ∏ t, dens (sgnMat r X.p0) (coords X κ z t) := by
  rw [densF, ← κ.prod_comp]
  exact Finset.prod_congr rfl fun t _ => Finset.prod_congr rfl fun i _ => by rw [dmin_cpt X κ z t]

/- English proof (translation)
Establish `hS'` using `measurable_proj X hj κ hS`. Use `set c := MeasurableEquiv.curry Tau (Fin j × Fin (r - j)) ℂ with hc`. Use `set φ : (Tau → Fin j × Fin (r - j) → ℂ) → ℝ≥0∞ := (c.symm ⁻¹' S).indicator 1 with hφ`. Establish `hφm : Measurable φ` using `measurable_one.indicator (c.symm.measurable hS)`. Establish `hDm : Measurable fun y => ENNReal.ofReal (dens (sgnMat r (r - j)) y)` using `(measurable_dens _).ennreal_ofReal`.

Establish `key` using `GlobalTheory.T.lintegral_pi_fibre_measurePreserving Tau _ _ _ (glue (idx hj)) (base (idx hj)) _ φ (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ _ (isBlockOrderedSumEquiv_trueIndex hj)) (measurable_base _) (base_glue (isBlockOrderedSumEquiv_trueIndex hj)) hD …`. Establish `hm : Measurable fun y : Tau → Low r → ℂ => φ (fun t => base (idx hj) (y t)) * ∏ t, ENNReal.ofReal (dens (sgnMat r (r - j)) (y t))` using `(hφm.comp (measurable_pi_lambda _ fun t => (measurable_base _).comp (measurable_pi_apply t))).mul (Finset.measurable_prod _ fun t _ => hDm.comp (measurable_pi_apply t))`. Rewrite `key` using `[← (GlobalTheory.T.measurePreserving_flagFibreChartCoordinates E r X Tau κ).lintegral_comp hm, ← (measurePreserving_curry Tau (Fin j × Fin (r - j))).lintegral_comp_emb c.measurableEmbedding]`. Rewrite using `[muF, muD, withDensity_apply _ hS', withDensity_apply _ hS, Measure.restrict_restrict hS', Measure.restrict_restrict hS, Set.inter_eq_left.2 hD, inter_OmF X hj κ hp hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_indicator hS', ← lintegral_indicator hS]`. Use `Eq.trans (lintegral_congr fun z => ?_) (key.trans (lintegral_congr fun v => ?_))` and prove the remaining obligations.

Establish `e : c.symm (fun t => base (idx hj) (coords X κ z t)) = proj X hj κ z`. Use function extensionality and compare the values at `fun s => (proj_eq X hj κ z s.1 s.2).symm`. Distinguish the cases in `h : proj X hj κ z ∈ S`. Rewrite using `[Set.indicator_of_mem (show z ∈ proj X hj κ ⁻¹' S from h), hφ, Set.indicator_of_mem (by rwa [Set.mem_preimage, e]), Pi.one_apply, one_mul, densF_eq X κ, hp, ENNReal.ofReal_prod_of_nonneg fun _ _ => dens_nonneg _ _]`. Rewrite using `[Set.indicator_of_notMem (show z ∉ proj X hj κ ⁻¹' S from h), hφ, Set.indicator_of_notMem (by rwa [Set.mem_preimage, e]), zero_mul]`.

Distinguish the cases in `h : v ∈ S`. Rewrite using `[Set.indicator_of_mem h, hφ, Set.indicator_of_mem (show c v ∈ c.symm ⁻¹' S from h), Pi.one_apply, one_mul]`. Establish `hc0 : 0 < flagConst j * flagConst (r - j)` using `mul_pos (flagConst_pos _) (flagConst_pos _)`. Establish `hv : ∀ t, toMat (c v t) ∈ hcDom j (r - j)` using `hD h`. Establish `hpos : ∀ t, 0 ≤ (hQ (toMat (c v t))).det.re ^ (-((j + (r - j) : ℕ) : ℤ))` using `fun t => zpow_nonneg (Complex.pos_iff.1 (PosDef.det_pos (hv t))).1.le _`.

Rewrite using `[Finset.prod_congr rfl fun t _ => GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) (sgnMat r (r - j)) (reindex_sgn hj) (c v t) (hv t), ← ENNReal.ofReal_prod_of_nonneg fun t _ => div_nonneg (hpos t) hc0.le, ← ENNRe …`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem h, hφ, Set.indicator_of_notMem (show c v ∉ c.symm ⁻¹' S from h), zero_mul]`.
-/
theorem muF_preimage (hp : X.p0 = r - j) {S : Set (Tau × Fin j × Fin (r - j) → ℂ)} (hS : MeasurableSet S)
    (hD : S ⊆ DomFlat Tau j (r - j)) :
    muF X (x0F X) (proj X hj κ ⁻¹' S) =
      ENNReal.ofReal ((flagConst j * flagConst (r - j))⁻¹ ^ Fintype.card Tau) * muD Tau j (r - j) S := by
  have hS' := measurable_proj X hj κ hS
  set c := MeasurableEquiv.curry Tau (Fin j × Fin (r - j)) ℂ with hc
  set φ : (Tau → Fin j × Fin (r - j) → ℂ) → ℝ≥0∞ := (c.symm ⁻¹' S).indicator 1 with hφ
  have hφm : Measurable φ := measurable_one.indicator (c.symm.measurable hS)
  have hDm : Measurable fun y => ENNReal.ofReal (dens (sgnMat r (r - j)) y) := (measurable_dens _).ennreal_ofReal
  have key := GlobalTheory.T.lintegral_pi_fibre_measurePreserving Tau _ _ _ (glue (idx hj)) (base (idx hj)) _ φ (GlobalTheory.T.measurePreserving_glueLowerUnitriangularBlocks _ _ _ _ (isBlockOrderedSumEquiv_trueIndex hj))
    (measurable_base _) (base_glue (isBlockOrderedSumEquiv_trueIndex hj)) hDm hφm
  have hm : Measurable fun y : Tau → Low r → ℂ => φ (fun t => base (idx hj) (y t)) *
      ∏ t, ENNReal.ofReal (dens (sgnMat r (r - j)) (y t)) :=
    (hφm.comp (measurable_pi_lambda _ fun t => (measurable_base _).comp (measurable_pi_apply t))).mul
      (Finset.measurable_prod _ fun t _ => hDm.comp (measurable_pi_apply t))
  rw [← (GlobalTheory.T.measurePreserving_flagFibreChartCoordinates E r X Tau κ).lintegral_comp hm,
    ← (measurePreserving_curry Tau (Fin j × Fin (r - j))).lintegral_comp_emb c.measurableEmbedding] at key
  rw [muF, muD, withDensity_apply _ hS', withDensity_apply _ hS, Measure.restrict_restrict hS',
    Measure.restrict_restrict hS, Set.inter_eq_left.2 hD,
    inter_OmF X hj κ hp hD, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_indicator hS', ← lintegral_indicator hS]
  refine Eq.trans (lintegral_congr fun z => ?_) (key.trans (lintegral_congr fun v => ?_))
  · have e : c.symm (fun t => base (idx hj) (coords X κ z t)) = proj X hj κ z :=
      funext fun s => (proj_eq X hj κ z s.1 s.2).symm
    by_cases h : proj X hj κ z ∈ S
    · rw [Set.indicator_of_mem (show z ∈ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_mem (by rwa [Set.mem_preimage, e]), Pi.one_apply, one_mul, densF_eq X κ, hp,
        ENNReal.ofReal_prod_of_nonneg fun _ _ => dens_nonneg _ _]
    · rw [Set.indicator_of_notMem (show z ∉ proj X hj κ ⁻¹' S from h), hφ,
        Set.indicator_of_notMem (by rwa [Set.mem_preimage, e]), zero_mul]
  · by_cases h : v ∈ S
    · rw [Set.indicator_of_mem h, hφ, Set.indicator_of_mem (show c v ∈ c.symm ⁻¹' S from h), Pi.one_apply, one_mul]
      have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
      have hv : ∀ t, toMat (c v t) ∈ hcDom j (r - j) := hD h
      have hpos : ∀ t, 0 ≤ (hQ (toMat (c v t))).det.re ^ (-((j + (r - j) : ℕ) : ℤ)) := fun t =>
        zpow_nonneg (Complex.pos_iff.1 (PosDef.det_pos (hv t))).1.le _
      rw [Finset.prod_congr rfl fun t _ => GlobalTheory.T.lintegral_flagDensity_fibre_boundedDomain r j (r - j) (idx hj) (isBlockOrderedSumEquiv_trueIndex hj) (sgnMat r (r - j))
        (reindex_sgn hj) (c v t) (hv t), ← ENNReal.ofReal_prod_of_nonneg fun t _ => div_nonneg (hpos t) hc0.le,
        ← ENNReal.ofReal_mul (by positivity), Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ,
        div_eq_inv_mul, inv_pow]
      rfl
    · rw [Set.indicator_of_notMem h, hφ, Set.indicator_of_notMem (show c v ∉ c.symm ⁻¹' S from h), zero_mul]

/- English proof (translation)
Introduce `E _ _ _ r j X hj Tau _ κ hp F hF`. Take `⟨F', hm, hsub, h0, hfs⟩` from `GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain E r j X hj Tau κ hp (GlobalTheory.T.domain_point_stabilizer_trivial E r j X hj Tau κ hp) (fun N hN hD h => by rw [muF_preimage X hj κ hp hN hD, h, mul_zero]) F hF`. Establish `hD` using `hsub.trans hF.2.1`. Rewrite `hfs` using `[inter_OmF X hj κ hp hD]`. Take `⟨h1, h2⟩` from `covol_eq X (isOrth_x0F X) hfs`.

Establish `e : muD Tau j (r - j) F' = muD Tau j (r - j) F` using `(measure_eq_measure_of_null_diff hsub h0)`. Establish `hc0 : 0 < flagConst j * flagConst (r - j)` using `mul_pos (flagConst_pos _) (flagConst_pos _)`. Rewrite `h1`, `h2` using `[muF_preimage X hj κ hp hm hD, e]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `lt_top_iff_ne_top.2 fun h => h1.ne ?_` and prove the remaining obligations.

Rewrite using `[h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']`. Establish `e1 : flagConst r = grassConst j (r - j) * (flagConst j * flagConst (r - j))`. Rewrite using `[← mul_assoc, ← flagConst_add, Nat.add_sub_cancel' hj]`. Establish `e2 : X.Ψ.card = Fintype.card Tau` using `by rw [Fintype.card_congr κ, Fintype.card_coe]`. Rewrite using `[h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), e1, e2, mul_pow, inv_pow]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem covol_eq_muD : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r j : ℕ) (X : Data E r) (hj : j ≤ r)
    (Tau : Type) [Fintype Tau] (κ : Tau ≃ X.Ψ), X.p0 = r - j → ∀ F, IsFD (gammaU X hj κ) F →
    muD Tau j (r - j) F < ⊤ ∧
      covol X = grassConst j (r - j) ^ Fintype.card Tau * (muD Tau j (r - j) F).toReal := by
  intro E _ _ _ r j X hj Tau _ κ hp F hF
  obtain ⟨F', hm, hsub, h0, hfs⟩ := GlobalTheory.T.isFundamentalSet_chart_preimage_fundamentalDomain E r j X hj Tau κ hp (GlobalTheory.T.domain_point_stabilizer_trivial E r j X hj Tau κ hp)
    (fun N hN hD h => by rw [muF_preimage X hj κ hp hN hD, h, mul_zero]) F hF
  have hD := hsub.trans hF.2.1
  rw [inter_OmF X hj κ hp hD] at hfs
  obtain ⟨h1, h2⟩ := covol_eq X (isOrth_x0F X) hfs
  have e : muD Tau j (r - j) F' = muD Tau j (r - j) F := (measure_eq_measure_of_null_diff hsub h0)
  have hc0 : 0 < flagConst j * flagConst (r - j) := mul_pos (flagConst_pos _) (flagConst_pos _)
  rw [muF_preimage X hj κ hp hm hD, e] at h1 h2
  refine ⟨?_, ?_⟩
  · refine lt_top_iff_ne_top.2 fun h => h1.ne ?_
    rw [h, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
  · have e1 : flagConst r = grassConst j (r - j) * (flagConst j * flagConst (r - j)) := by
      rw [← mul_assoc, ← flagConst_add, Nat.add_sub_cancel' hj]
    have e2 : X.Ψ.card = Fintype.card Tau := by rw [Fintype.card_congr κ, Fintype.card_coe]
    rw [h2, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), e1, e2, mul_pow, inv_pow]
    field_simp

end GlobalTheory.FlagFibre
