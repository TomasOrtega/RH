import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosurePropertiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdelicHaarSplitsAsArchTimesFiniteStatement

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix NNReal ENNReal

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨⟨laminf, hinf⟩, hlamex⟩` from `GlobalTheory.T.exists_standard_local_measures F`. Use `choose lam hlam using hlamex`. Take `⟨lf, hlf, h1⟩` from `GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F`. Take `⟨cinf, c, hU, hci, hcv⟩` from `GlobalTheory.CompanionTheory.SW.SdTuples.sdW_coord F E σ hCM M J hJ d bs laminf lam hinf hlam ψ hψ n`. Establish `eμi : μi = cinf • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) bs laminf n M` using `(hci μi).1 hμi`.

Establish `eμv : ∀ v, μv v = c v • GlobalTheory.CompanionTheory.SW.coordW (Fv F v) bs (lam v) n M` using `fun v => (hcv v (μv v)).1 (hμv v)`. Establish `hc0 : ∀ v, c v ≠ 0` using `(GlobalTheory.T.unit_product_closure_properties F cinf cinf c c hU hU).2.1`. Establish `hfin : {v | ¬ c v = 1}.Finite` using `Filter.eventually_cofinite.1 hU.1`. Use `⟨hfin.toFinset, fun S hS gi g hg => ?_⟩` and prove the remaining obligations. Establish `hsupp : Function.mulSupport c ⊆ (S : Set (HeightOneSpectrum (𝓞 F)))`.

Introduce `v hv`. Conclude with `hS (hfin.mem_toFinset.2 hv)`. Establish `hprod1 : cinf * ∏ v ∈ S, c v = 1`. Rewrite using `[← finprod_eq_prod_of_mulSupport_subset c hsupp]`. Conclude with `hU.2`.

Take `⟨-, hAfLC, hAfSC, hAfT2⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Use `haveI : BorelSpace (Af F) := ⟨rfl⟩`. Establish `hBv : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E)` using `fun v => by`. Take `⟨t1, t2, t3, t4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Conclude with `(GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M`.

Establish `hSFv : ∀ v, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) bs (lam v) n M)` using `fun v => by`. Take `⟨t1, t2, t3, t4, -⟩` from `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Use `haveI := (hlam v).1`. Establish `hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F` using `F) (E := E) (Fv F v) bs) := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.1 d bs`.

Use `haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Fv F v) hK (lam v)`. Unfold `GlobalTheory.CompanionTheory.SW.coordW`. Use `infer_instance`. Establish `hcV : ∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _)` using `(GlobalTheory.T.adelic_tuple_projections F E σ hCM d bs n M).2.2.1`. Use `haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M`.

Establish `hpv : ∀ v, Measurable (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _)` using `fun v => by haveI := hBv v`. Conclude with `(hcV v).measurable`. Establish `hlat` using `GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ hCM bs n M`. Use `set A : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ v, v ∉ S → projV v Y ∈ latV bs v} with hA`. Establish `hAm : MeasurableSet A`.

Establish `: A = ⋂ v, ⋂ (_ : v ∉ S), projV v ⁻¹' latV bs v`. Use extensionality with `Y`. Simplify using `[hA]`. Rewrite using `[this]`. Conclude with `MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hpv v (hlat v)`.

Set `ρ : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E)` to `fun Y v => projV v.1 Y`. Establish `hρ : Measurable ρ` using `measurable_pi_lambda _ fun v => hpv v.1`. Use `haveI : ∀ v : S, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M) := fun v => hSFv v.1`. Establish `hmap : ((GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M).restrict A).map ρ = Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M`. Use `symm`.

Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.map_apply hρ (MeasurableSet.univ_pi hs), Measure.restrict_apply (hρ (MeasurableSet.univ_pi hs))]`. Set `A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)` to `fun v => if h : v ∈ S then s ⟨v, h⟩ else Set.univ`. Establish `hA' : ∀ v, MeasurableSet (A' v)` using `fun v => by`. Distinguish the cases in `h : v ∈ S`.

Simplify using `only [A', dif_pos h]`. Conclude with `hs _`. Simplify using `only [A', dif_neg h]`. Conclude with `MeasurableSet.univ`. Establish `key` using `GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d bs lam hlam lf hlf h1 n M S A' hA'`.

Establish `hset : ρ ⁻¹' Set.univ.pi s ∩ A = {X | (∀ v ∈ S, projV v X ∈ A' v) ∧ ∀ v, v ∉ S → projV v X ∈ latV bs v}`. Use extensionality with `X`. Simplify using `only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, hA, Set.mem_setOf_eq]`. Use `and_congr_left fun _ => ⟨fun h v hv => ?_, fun h v => ?_⟩` and prove the remaining obligations. Simplify `h ⟨v, hv⟩` using `only [A', dif_pos hv]`.

Use `h v.1 v.2` as an intermediate fact. Simplify `this` using `only [A', dif_pos v.2]`. Rewrite using `[hset, key, ← Finset.prod_coe_sort S]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Simplify using `only [A', dif_pos v.2]`.

Establish `hgc : ∀ v : S, AEStronglyMeasurable (g v.1) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M)`. Introduce `v`. Establish `h` using `hg v.1 v.2`. Rewrite `h` using `[eμv v.1]`. Establish `hac : GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M ≪ (c v.1 • GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M)`.

Establish `h2` using `Measure.absolutelyContinuous_smul (μ := GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M) (c := ((c v.1 : ℝ≥0) : ℝ≥0∞)) (by exact_mod_cast hc0 v.1)`. Introduce `t ht`. Use `h2 ht` as an intermediate fact. Simplify `this` using `[ENNReal.smul_def]`. Conclude with `h.mono_ac hac`.

Establish `hGm : AEStronglyMeasurable (fun y : (∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E)) => ∏ v : S, g v.1 (y v)) (Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M)` using `(Finset.aestronglyMeasurable_prod Finset.univ fun v _ => (hgc v).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ v)).congr (Filter.Eventually.of_forall fun y => by simp [Finset.prod_apply])`. Establish `hfinI : ∫ y, A.indicator (fun y => ∏ v ∈ S, g v (projV v y)) y ∂(GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M) = ∏ v ∈ S, ∫ x, g v x ∂(GlobalTheory.CompanionTheory.SW.coordW (Fv F v) bs (lam v) n M)`. Rewrite using `[integral_indicator hAm]`. Establish `e1 : ∫ y in A, ∏ v ∈ S, g v (projV v y) ∂(GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M) = ∫ y, ∏ v : S, g v.1 (y v) ∂(((GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M).restrict A).map ρ)`. Rewrite using `[integral_map hρ.aemeasurable (by rw [hmap]; exact hGm)]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)` and prove the remaining obligations. Simplify using `only [ρ]`. Rewrite using `[← Finset.prod_coe_sort S]`. Rewrite using `[e1, hmap, integral_fintype_prod_eq_prod (fun v : S => g v.1), ← Finset.prod_coe_sort S]`. Take `⟨-, -, -, -, -, -, -, -, hme, -⟩` from `GlobalTheory.T.adelic_haar_splits_as_arch_times_finite F E σ hCM M n μ hμ.1`.

Use `haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M) := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.sfinite_coordW σ hCM bs lf hlf n M`. Use `haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) bs laminf n M) := by haveI : BorelSpace (Ainf F) := ⟨rfl⟩ haveI := hinf.1`. Establish `hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F` using `F) (E := E) (Ainf F) bs) := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.1 d bs`. Use `haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Ainf F) hK laminf`. Unfold `GlobalTheory.CompanionTheory.SW.coordW`.

Use `infer_instance`. Establish `hme' : MeasurableEmbedding (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X))` using `hme`. Establish `hT` using `GlobalTheory.CompanionTheory.SiegelND.DxN.dx_splitN σ hCM M J hJ ψ hψ n μ hμ bs laminf hinf lf hlf h1`. Set `G : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) → ℂ` to `fun p => gi p.1 * A.indicator (fun y => ∏ v ∈ S, g v (projV v y)) p.2`. Establish `hpt : ∀ X, (GlobalTheory.CompanionTheory.SW.intOff bs S).indicator (fun X => gi (projInf X) * ∏ v ∈ S, g v (projV v (projFin X))) X = G (projInf X, projFin X)`.

Introduce `X`. Distinguish the cases in `hX : X ∈ GlobalTheory.CompanionTheory.SW.intOff bs S`. Establish `hX' : projFin X ∈ A` using `hX`. Simplify using `only [G, Set.indicator_of_mem hX, Set.indicator_of_mem hX']`. Establish `hX' : projFin X ∉ A` using `hX`.

Simplify using `only [G, Set.indicator_of_notMem hX, Set.indicator_of_notMem hX', mul_zero]`. Establish `hL : ∫ X, (GlobalTheory.CompanionTheory.SW.intOff bs S).indicator (fun X => gi (projInf X) * ∏ v ∈ S, g v (projV v (projFin X))) X ∂μ = (∫ x, gi x ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) bs laminf n M)) * ∏ v ∈ S, ∫ x, g v x ∂(GlobalTheory.CompanionTheory.SW.coordW (Fv …`. Repeatedly rewrite using `[hpt]`. Rewrite using `[← hme'.integral_map, hT.map_eq]`. Simplify using `only [G]`.

Rewrite using `[integral_prod_mul gi (fun y => A.indicator (fun y => ∏ v ∈ S, g v (projV v y)) y), hfinI]`. Rewrite using `[hL, eμi, integral_smul_nnreal_measure]`. Repeatedly rewrite using `[eμv, integral_smul_nnreal_measure]`. Rewrite using `[Finset.prod_congr rfl (fun v _ => NNReal.smul_def (c v) _), Finset.prod_congr rfl (fun v _ => Complex.real_smul)]`. Rewrite using `[NNReal.smul_def, Complex.real_smul, Finset.prod_mul_distrib]`.

Establish `hc1 : ((cinf : ℝ) : ℂ) * ∏ v ∈ S, ((c v : ℝ) : ℂ) = 1`. Establish `: ((cinf * ∏ v ∈ S, c v : ℝ≥0) : ℝ) = 1` using `by rw [hprod1]; simp`. Move the coercions through the operations in `at this`. Conclude with `this` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation.
-/
theorem tup_split (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) (M n d : ℕ)
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (bs : Module.Basis (Fin d) F E)
    (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)) (hμ : SdW F E σ M J (AF F) ψ n μ)
    (μi : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (hμi : SdW F E σ M J (Ainf F) (psiInf F ψ) n μi)
    (μv : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E))
    (hμv : ∀ v, SdW F E σ M J (Fv F v) (psiV F ψ v) n (μv v)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      ∀ (gi : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ) (g : ∀ v : HeightOneSpectrum (𝓞 F), (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ),
        (∀ v ∈ S, AEStronglyMeasurable (g v) (μv v)) →
        ∫ X, (GlobalTheory.CompanionTheory.SW.intOff bs S).indicator (fun X => gi (projInf X) * ∏ v ∈ S, g v (projV v (projFin X))) X ∂μ =
          (∫ x, gi x ∂μi) * ∏ v ∈ S, ∫ x, g v x ∂(μv v) := by
  classical
  obtain ⟨⟨laminf, hinf⟩, hlamex⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlamex
  obtain ⟨lf, hlf, h1⟩ := GlobalTheory.CompanionTheory.AdeleHaar.exists_haar_integral_one F
  obtain ⟨cinf, c, hU, hci, hcv⟩ := GlobalTheory.CompanionTheory.SW.SdTuples.sdW_coord F E σ hCM M J hJ d bs laminf lam hinf hlam ψ hψ n
  have eμi : μi = cinf • GlobalTheory.CompanionTheory.SW.coordW (Ainf F) bs laminf n M := (hci μi).1 hμi
  have eμv : ∀ v, μv v = c v • GlobalTheory.CompanionTheory.SW.coordW (Fv F v) bs (lam v) n M := fun v => (hcv v (μv v)).1 (hμv v)
  have hc0 : ∀ v, c v ≠ 0 := (GlobalTheory.T.unit_product_closure_properties F cinf cinf c c hU hU).2.1
  have hfin : {v | ¬ c v = 1}.Finite := Filter.eventually_cofinite.1 hU.1
  refine ⟨hfin.toFinset, fun S hS gi g hg => ?_⟩

  have hsupp : Function.mulSupport c ⊆ (S : Set (HeightOneSpectrum (𝓞 F))) := by
    intro v hv
    exact hS (hfin.mem_toFinset.2 hv)
  have hprod1 : cinf * ∏ v ∈ S, c v = 1 := by
    rw [← finprod_eq_prod_of_mulSupport_subset c hsupp]
    exact hU.2

  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  have hBv : ∀ v, BorelSpace (Fin n → Fin M → Fv F v ⊗[F] E) := fun v => by
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    exact (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  have hSFv : ∀ v, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) bs (lam v) n M) := fun v => by
    obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    haveI := (hlam v).1
    have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Fv F v) bs) :=
      (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Fv F v)).2.2.2.2.2.2.1 d bs
    haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Fv F v) hK (lam v)
    unfold GlobalTheory.CompanionTheory.SW.coordW
    infer_instance
  have hcV : ∀ v, Continuous (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) :=
    (GlobalTheory.T.adelic_tuple_projections F E σ hCM d bs n M).2.2.1
  haveI hBf := (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Af F)).2.2.2.2.2.2.2.1 n M
  have hpv : ∀ v, Measurable (projV v : (Fin n → Fin M → Af F ⊗[F] E) → _) := fun v => by
    haveI := hBv v
    exact (hcV v).measurable
  have hlat := GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.measurableSet_latV σ hCM bs n M
  set A : Set (Fin n → Fin M → Af F ⊗[F] E) := {Y | ∀ v, v ∉ S → projV v Y ∈ latV bs v} with hA
  have hAm : MeasurableSet A := by
    have : A = ⋂ v, ⋂ (_ : v ∉ S), projV v ⁻¹' latV bs v := by
      ext Y; simp [hA]
    rw [this]
    exact MeasurableSet.iInter fun v => MeasurableSet.iInter fun _ => hpv v (hlat v)

  let ρ : (Fin n → Fin M → Af F ⊗[F] E) → ∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E) := fun Y v => projV v.1 Y
  have hρ : Measurable ρ := measurable_pi_lambda _ fun v => hpv v.1
  haveI : ∀ v : S, SigmaFinite (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M) := fun v => hSFv v.1
  have hmap : ((GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M).restrict A).map ρ =
      Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M := by
    symm
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.map_apply hρ (MeasurableSet.univ_pi hs), Measure.restrict_apply (hρ (MeasurableSet.univ_pi hs))]
    let A' : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
      fun v => if h : v ∈ S then s ⟨v, h⟩ else Set.univ
    have hA' : ∀ v, MeasurableSet (A' v) := fun v => by
      by_cases h : v ∈ S
      · simp only [A', dif_pos h]; exact hs _
      · simp only [A', dif_neg h]; exact MeasurableSet.univ
    have key := GlobalTheory.CompanionTheory.SW.WBox.coordW_box F E σ hCM d bs lam hlam lf hlf h1 n M S A' hA'
    have hset : ρ ⁻¹' Set.univ.pi s ∩ A = {X | (∀ v ∈ S, projV v X ∈ A' v) ∧ ∀ v, v ∉ S → projV v X ∈ latV bs v} := by
      ext X
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, hA, Set.mem_setOf_eq]
      refine and_congr_left fun _ => ⟨fun h v hv => ?_, fun h v => ?_⟩
      · simpa only [A', dif_pos hv] using h ⟨v, hv⟩
      · have := h v.1 v.2
        simpa only [A', dif_pos v.2] using this
    rw [hset, key, ← Finset.prod_coe_sort S]
    refine Finset.prod_congr rfl fun v _ => ?_
    simp only [A', dif_pos v.2]

  have hgc : ∀ v : S, AEStronglyMeasurable (g v.1) (GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M) := by
    intro v
    have h := hg v.1 v.2
    rw [eμv v.1] at h
    have hac : GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M ≪ (c v.1 • GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M) := by
      have h2 := Measure.absolutelyContinuous_smul (μ := GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M)
        (c := ((c v.1 : ℝ≥0) : ℝ≥0∞)) (by exact_mod_cast hc0 v.1)
      intro t ht
      have := h2 ht
      simpa [ENNReal.smul_def] using this
    exact h.mono_ac hac
  have hGm : AEStronglyMeasurable (fun y : (∀ v : S, (Fin n → Fin M → Fv F v.1 ⊗[F] E)) => ∏ v : S, g v.1 (y v))
      (Measure.pi fun v : S => GlobalTheory.CompanionTheory.SW.coordW (Fv F v.1) bs (lam v.1) n M) :=
    (Finset.aestronglyMeasurable_prod Finset.univ fun v _ =>
      (hgc v).comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_eval _ v)).congr
        (Filter.Eventually.of_forall fun y => by simp [Finset.prod_apply])
  have hfinI : ∫ y, A.indicator (fun y => ∏ v ∈ S, g v (projV v y)) y ∂(GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M) =
      ∏ v ∈ S, ∫ x, g v x ∂(GlobalTheory.CompanionTheory.SW.coordW (Fv F v) bs (lam v) n M) := by
    rw [integral_indicator hAm]
    have e1 : ∫ y in A, ∏ v ∈ S, g v (projV v y) ∂(GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M) =
        ∫ y, ∏ v : S, g v.1 (y v) ∂(((GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M).restrict A).map ρ) := by
      rw [integral_map hρ.aemeasurable (by rw [hmap]; exact hGm)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun Y => ?_)
      simp only [ρ]
      rw [← Finset.prod_coe_sort S]
    rw [e1, hmap, integral_fintype_prod_eq_prod (fun v : S => g v.1), ← Finset.prod_coe_sort S]

  obtain ⟨-, -, -, -, -, -, -, -, hme, -⟩ := GlobalTheory.T.adelic_haar_splits_as_arch_times_finite F E σ hCM M n μ hμ.1
  haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordW (Af F) bs lf n M) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.OneV.DxEuler.sfinite_coordW σ hCM bs lf hlf n M
  haveI : SFinite (GlobalTheory.CompanionTheory.SW.coordW (Ainf F) bs laminf n M) := by
    haveI : BorelSpace (Ainf F) := ⟨rfl⟩
    haveI := hinf.1
    have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Ainf F) bs) :=
      (GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM (Ainf F)).2.2.2.2.2.2.1 d bs
    haveI := GlobalTheory.CompanionTheory.SW.WBox.sigmaFinite_coordK (Ainf F) hK laminf
    unfold GlobalTheory.CompanionTheory.SW.coordW
    infer_instance
  have hme' : MeasurableEmbedding (fun X : Fin n → Fin M → AF F ⊗[F] E => (projInf X, projFin X)) := hme
  have hT := GlobalTheory.CompanionTheory.SiegelND.DxN.dx_splitN σ hCM M J hJ ψ hψ n μ hμ bs laminf hinf lf hlf h1
  let G : (Fin n → Fin M → Ainf F ⊗[F] E) × (Fin n → Fin M → Af F ⊗[F] E) → ℂ :=
    fun p => gi p.1 * A.indicator (fun y => ∏ v ∈ S, g v (projV v y)) p.2
  have hpt : ∀ X, (GlobalTheory.CompanionTheory.SW.intOff bs S).indicator (fun X => gi (projInf X) * ∏ v ∈ S, g v (projV v (projFin X))) X =
      G (projInf X, projFin X) := by
    intro X
    by_cases hX : X ∈ GlobalTheory.CompanionTheory.SW.intOff bs S
    · have hX' : projFin X ∈ A := hX
      simp only [G, Set.indicator_of_mem hX, Set.indicator_of_mem hX']
    · have hX' : projFin X ∉ A := hX
      simp only [G, Set.indicator_of_notMem hX, Set.indicator_of_notMem hX', mul_zero]
  have hL : ∫ X, (GlobalTheory.CompanionTheory.SW.intOff bs S).indicator (fun X => gi (projInf X) * ∏ v ∈ S, g v (projV v (projFin X))) X ∂μ =
      (∫ x, gi x ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) bs laminf n M)) *
        ∏ v ∈ S, ∫ x, g v x ∂(GlobalTheory.CompanionTheory.SW.coordW (Fv F v) bs (lam v) n M) := by
    simp_rw [hpt]
    rw [← hme'.integral_map, hT.map_eq]
    simp only [G]
    rw [integral_prod_mul gi (fun y => A.indicator (fun y => ∏ v ∈ S, g v (projV v y)) y), hfinI]
  rw [hL, eμi, integral_smul_nnreal_measure]
  simp_rw [eμv, integral_smul_nnreal_measure]
  rw [Finset.prod_congr rfl (fun v _ => NNReal.smul_def (c v) _), Finset.prod_congr rfl (fun v _ => Complex.real_smul)]
  rw [NNReal.smul_def, Complex.real_smul, Finset.prod_mul_distrib]
  have hc1 : ((cinf : ℝ) : ℂ) * ∏ v ∈ S, ((c v : ℝ) : ℂ) = 1 := by
    have : ((cinf * ∏ v ∈ S, c v : ℝ≥0) : ℝ) = 1 := by rw [hprod1]; simp
    push_cast at this
    exact_mod_cast this
  calc _ = (((cinf : ℝ) : ℂ) * ∏ v ∈ S, ((c v : ℝ) : ℂ)) * ((∫ x, gi x ∂(GlobalTheory.CompanionTheory.SW.coordW (Ainf F) bs laminf n M)) *
        ∏ v ∈ S, ∫ x, g v x ∂(GlobalTheory.CompanionTheory.SW.coordW (Fv F v) bs (lam v) n M)) := by rw [hc1, one_mul]
    _ = _ := by ring

end PositivityTheory.SiegelWeilFormula.GFac

end
