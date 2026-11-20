import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsWeilFormulas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPoissonSummationAnyHaar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAdelesHaarMeasureCovolumeOne
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NullOfFiniteCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsGoodModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerIntertwinerScalar
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit

noncomputable section

namespace GlobalTheory.AdelicFourierSch

open Filter GlobalTheory.WeylFourier GlobalTheory.RatWeilOp GlobalTheory.WeylBij

open scoped Classical in

/- English proof (translation)
Establish `hunr` using `psiUnr_eventually ψ hψ`. Use `letI mI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _`. Use `haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩`. Use `letI mV : ∀ v : Pl F, MeasurableSpace (κ → Fv F v) := fun _ => borel _`. Use `haveI bV : ∀ v : Pl F, BorelSpace (κ → Fv F v) := fun _ => ⟨rfl⟩`.

Take `⟨μi, hμi⟩ : ∃ μ : Measure (κ → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure` from `⟨Measure.addHaar, inferInstance⟩`. Choose the witnesses or unpack the hypotheses as in `⟨μv, hμv, hμv1⟩ : ∃ μv : ∀ v : Pl F, Measure (κ → Fv F v), (∀ v, (μv v).IsAddHaarMeasure) ∧ ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := by`. Set `K : ∀ v : Pl F, TopologicalSpace.PositiveCompacts (κ → Fv F v)` to `fun v => ⟨⟨Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)), isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v⟩, by show (interior (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Se …`. Rewrite using `[(isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).interior_eq]`. Conclude with `⟨0, fun i _ => (v.adicCompletionIntegers F).zero_mem⟩⟩`.

Use `⟨fun v => Measure.addHaarMeasure (K v), fun v => inferInstance, fun v => ?_⟩` and prove the remaining obligations. Establish `e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = (K v : Set (κ → Fv F v))`. Use extensionality with `x`. Simplify using `[K]`. Rewrite using `[e]`.

Conclude with `Measure.addHaarMeasure_self`. Use `haveI := hμv`. Take `⟨c₀, hc₀, hpure⟩` from `GlobalTheory.T.integral_adelic_pureTensor_eq_product_local F κ μ μi μv hμv1`. Take `⟨ei', hei'bij, hei'⟩` from `GlobalTheory.T.exists_archimedeanSchwartz_traceFourier_bijective F κ μi`. Establish `hψc : ∀ v, Continuous (GlobalTheory.LatVac.psiAt ψ v)` using `fun v => GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v`.

Establish `hsub : ∀ v, ∀ φ ∈ SB (κ → Fv F v), φ ∈ intSub (GlobalTheory.LatVac.psiAt ψ v) (μv v)` using `fun v φ hφ y => (hφ.1.continuous.mul ((hψc v).comp (continuous_id.dotProduct continuous_const))).integrable_of_hasCompactSupport hφ.2.mul_right`. Set `ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ` to `fun v => ftE (GlobalTheory.LatVac.psiAt ψ v) (μv v)`. Establish `hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = ft (GlobalTheory.LatVac.psiAt ψ v) (μv v) φ` using `fun v φ hφ => ftE_eq _ _ (hsub v φ hφ)`. Establish `hbij : ∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _)` using `fun v => (GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace F v (GlobalTheory.LatVac.psiAt ψ v) (hψc v) (fun t => GlobalTheory.StdCharFromIsStd.norm_psi hψ _) (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) κ (μv v)).congr fun φ hφ => (hev v φ hφ).symm`. Establish `hind : ∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v` using `by filter_upwards [hunr] with v hv`.

Rewrite using `[hev v (ind κ v) (GlobalTheory.StdVacuum.indicator_mem_SB v)]`. Conclude with `GlobalTheory.T.integralPointsIndicator_fourier_self_unramified F v (GlobalTheory.LatVac.psiAt ψ v) (fun x => hv x) κ (μv v) (hμv1 v)`. Establish `hpureE : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ intSub ψ μ ∧ ft ψ μ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensor …`. Introduce `f φ hφ`. Establish `hφ' : ∀ y, IsFam (finT ψ φ y)` using `finT_isFam ψ hψ φ hφ`.

Establish `hfun : ∀ y, (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y)) = fun x => archT f (fun i => evI F (y i)) (fun i => evI F (x i)) * ∏ᶠ v, finT ψ φ y v (fun i => evFin F v (x i))` using `fun y => funext fun x => pure_mul_psi ψ hψ f φ hφ x y`. Use `⟨fun y => ?_, funext fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[hfun y]`. Conclude with `(hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).1`. Use `show ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y) ∂μ = _`.

Rewrite using `[hfun y, (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).2]`. Establish `h2 : ∀ v, ev v (φ v) (fun i => evFin F v (y i)) = ∫ x, finT ψ φ y v x ∂(μv v)` using `fun v => by`. Rewrite using `[hev v _ (hφ.1 v)]`. Both sides reduce to the same expression. Establish `h3 : (c₀ • ei' f) (fun i => evI F (y i)) = c₀ * ∫ x, archT f (fun i => evI F (y i)) x ∂μi`.

Establish `h4` using `hei' f (fun i => evI F (y i))`. Simplify using `only [archT]`. Rewrite using `[← h4]`. Both sides reduce to the same expression. Use `show _ = (c₀ • ei' f) (fun i => evI F (y i)) * ∏ᶠ v, ev v (φ v) (fun i => evFin F v (y i))`.

Rewrite using `[h3, finprod_congr h2]`. Set `T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ` to `ftE ψ μ`. Establish `hfam : ∀ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, IsFam φ → IsFam fun v => ev v (φ v)` using `fun φ hφ => ⟨fun v => (hbij v).mapsTo (hφ.1 v), by filter_upwards [hφ.2, hind] with v h1 h2; rw [h1, h2]⟩`. Establish `hTpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ → T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v))` using `fun f φ hφ => (ftE_eq ψ μ (hpureE f φ hφ).1).trans (hpureE f φ hφ).2`. Establish `hgen` using `schA_le_span_pure F κ`.

Establish `hT_schA : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ`. Introduce `Φ hΦ`. Use `(Submodule.span_le.2 ?_ : _ ≤ (schA F κ).comap T) (hgen Φ hΦ)` and prove the remaining obligations. Introduce and unpack `_ ⟨f, φ, hφ, rfl⟩`. Use `show T _ ∈ schA F κ`.

Rewrite using `[hTpure f φ hφ]`. Conclude with `pure_mem_schA _ _ (hfam φ hφ)`. Establish `hint : ∀ Φ ∈ schA F κ, Φ ∈ intSub ψ μ` using `fun Φ hΦ => by`. Use `(Submodule.span_le.2 ?_ : _ ≤ intSub ψ μ) (hgen Φ hΦ)` and prove the remaining obligations. Introduce and unpack `_ ⟨f, φ, hφ, rfl⟩`.

Conclude with `(hpureE f φ hφ).1`. Introduce `Φ hΦ`. Establish `h` using `hT_schA Φ hΦ`. Rewrite `h` using `[show T Φ = ft ψ μ Φ from ftE_eq ψ μ (hint Φ hΦ)]`. Conclude with `h`.
-/
theorem fourier_mem_schA_std (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F))
    [μ.IsAddHaarMeasure] : ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  have hunr := psiUnr_eventually ψ hψ
  letI mI : MeasurableSpace (κ → mixedEmbedding.mixedSpace F) := borel _
  haveI : BorelSpace (κ → mixedEmbedding.mixedSpace F) := ⟨rfl⟩
  letI mV : ∀ v : Pl F, MeasurableSpace (κ → Fv F v) := fun _ => borel _
  haveI bV : ∀ v : Pl F, BorelSpace (κ → Fv F v) := fun _ => ⟨rfl⟩
  obtain ⟨μi, hμi⟩ : ∃ μ : Measure (κ → mixedEmbedding.mixedSpace F), μ.IsAddHaarMeasure :=
    ⟨Measure.addHaar, inferInstance⟩
  obtain ⟨μv, hμv, hμv1⟩ : ∃ μv : ∀ v : Pl F, Measure (κ → Fv F v), (∀ v, (μv v).IsAddHaarMeasure) ∧
      ∀ v, μv v {x | ∀ i, x i ∈ v.adicCompletionIntegers F} = 1 := by
    let K : ∀ v : Pl F, TopologicalSpace.PositiveCompacts (κ → Fv F v) := fun v =>
      ⟨⟨Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)),
        isCompact_univ_pi fun _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v⟩, by
          show (interior (Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)))).Nonempty
          rw [(isOpen_set_pi Set.finite_univ fun _ _ => ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v).interior_eq]
          exact ⟨0, fun i _ => (v.adicCompletionIntegers F).zero_mem⟩⟩
    refine ⟨fun v => Measure.addHaarMeasure (K v), fun v => inferInstance, fun v => ?_⟩
    have e : {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} = (K v : Set (κ → Fv F v)) := by
      ext x; simp [K]
    rw [e]
    exact Measure.addHaarMeasure_self
  haveI := hμv
  obtain ⟨c₀, hc₀, hpure⟩ := GlobalTheory.T.integral_adelic_pureTensor_eq_product_local F κ μ μi μv hμv1
  obtain ⟨ei', hei'bij, hei'⟩ := GlobalTheory.T.exists_archimedeanSchwartz_traceFourier_bijective F κ μi
  have hψc : ∀ v, Continuous (GlobalTheory.LatVac.psiAt ψ v) := fun v => GlobalTheory.SchrSB.continuous_psiAt ψ hψ.1 v
  have hsub : ∀ v, ∀ φ ∈ SB (κ → Fv F v), φ ∈ intSub (GlobalTheory.LatVac.psiAt ψ v) (μv v) := fun v φ hφ y =>
    (hφ.1.continuous.mul ((hψc v).comp (continuous_id.dotProduct continuous_const))).integrable_of_hasCompactSupport
      hφ.2.mul_right
  let ev : ∀ v : Pl F, ((κ → Fv F v) → ℂ) →ₗ[ℂ] (κ → Fv F v) → ℂ := fun v => ftE (GlobalTheory.LatVac.psiAt ψ v) (μv v)
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = ft (GlobalTheory.LatVac.psiAt ψ v) (μv v) φ :=
    fun v φ hφ => ftE_eq _ _ (hsub v φ hφ)
  have hbij : ∀ v, Set.BijOn (ev v) (SB (κ → Fv F v) : Set _) (SB (κ → Fv F v) : Set _) := fun v =>
    (GlobalTheory.T.fourier_bijOn_schwartzBruhat_finitePlace F v (GlobalTheory.LatVac.psiAt ψ v) (hψc v) (fun t => GlobalTheory.StdCharFromIsStd.norm_psi hψ _)
      (GlobalTheory.PsiNontriv.psiAt_ne_one ψ hψ v) κ (μv v)).congr fun φ hφ => (hev v φ hφ).symm
  have hind : ∀ᶠ v in cofinite, ev v (ind κ v) = ind κ v := by
    filter_upwards [hunr] with v hv
    rw [hev v (ind κ v) (GlobalTheory.StdVacuum.indicator_mem_SB v)]
    exact GlobalTheory.T.integralPointsIndicator_fourier_self_unramified F v (GlobalTheory.LatVac.psiAt ψ v) (fun x => hv x) κ (μv v) (hμv1 v)
  have hpureE : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ ∈ intSub ψ μ ∧
      ft ψ μ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := by
    intro f φ hφ
    have hφ' : ∀ y, IsFam (finT ψ φ y) := finT_isFam ψ hψ φ hφ
    have hfun : ∀ y, (fun x => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        archT f (fun i => evI F (y i)) (fun i => evI F (x i)) * ∏ᶠ v, finT ψ φ y v (fun i => evFin F v (x i)) :=
      fun y => funext fun x => pure_mul_psi ψ hψ f φ hφ x y
    refine ⟨fun y => ?_, funext fun y => ?_⟩
    · rw [hfun y]
      exact (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).1
    · show ∫ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ x * ψ (x ⬝ᵥ y) ∂μ = _
      rw [hfun y, (hpure _ _ (archT_continuous f _) (archT_integrable μi f _) (hφ' y)).2]
      have h2 : ∀ v, ev v (φ v) (fun i => evFin F v (y i)) = ∫ x, finT ψ φ y v x ∂(μv v) := fun v => by
        rw [hev v _ (hφ.1 v)]; rfl
      have h3 : (c₀ • ei' f) (fun i => evI F (y i)) = c₀ * ∫ x, archT f (fun i => evI F (y i)) x ∂μi := by
        have h4 := hei' f (fun i => evI F (y i))
        simp only [archT]
        rw [← h4]
        rfl
      show _ = (c₀ • ei' f) (fun i => evI F (y i)) * ∏ᶠ v, ev v (φ v) (fun i => evFin F v (y i))
      rw [h3, finprod_congr h2]
  let T : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ := ftE ψ μ
  have hfam : ∀ φ : ∀ v : Pl F, (κ → Fv F v) → ℂ, IsFam φ → IsFam fun v => ev v (φ v) := fun φ hφ =>
    ⟨fun v => (hbij v).mapsTo (hφ.1 v), by filter_upwards [hφ.2, hind] with v h1 h2; rw [h1, h2]⟩
  have hTpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ), IsFam φ →
      T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c₀ • ei' f) (fun v => ev v (φ v)) := fun f φ hφ =>
    (ftE_eq ψ μ (hpureE f φ hφ).1).trans (hpureE f φ hφ).2
  have hgen := schA_le_span_pure F κ
  have hT_schA : ∀ Φ ∈ schA F κ, T Φ ∈ schA F κ := by
    intro Φ hΦ
    refine (Submodule.span_le.2 ?_ : _ ≤ (schA F κ).comap T) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    show T _ ∈ schA F κ
    rw [hTpure f φ hφ]
    exact pure_mem_schA _ _ (hfam φ hφ)
  have hint : ∀ Φ ∈ schA F κ, Φ ∈ intSub ψ μ := fun Φ hΦ => by
    refine (Submodule.span_le.2 ?_ : _ ≤ intSub ψ μ) (hgen Φ hΦ)
    rintro _ ⟨f, φ, hφ, rfl⟩
    exact (hpureE f φ hφ).1
  intro Φ hΦ
  have h := hT_schA Φ hΦ
  rw [show T Φ = ft ψ μ Φ from ftE_eq ψ μ (hint Φ hΦ)] at h
  exact h

/- English proof (translation)
Establish `hdet : IsUnit (Matrix.diagonal fun _ : κ => a⁻¹).det`. Rewrite using `[Matrix.det_diagonal]`. Conclude with `(Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero ha).isUnit`. Establish `hinv : (Matrix.diagonal fun _ : κ => a⁻¹)⁻¹ = Matrix.diagonal fun _ : κ => a`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations.

Rewrite using `[Matrix.diagonal_mul_diagonal]`. Simplify using `[mul_inv_cancel₀ ha]`. Establish `h` using `GlobalTheory.SympChangeBij.levi_mapsTo _ hdet Φ hΦ`. Rewrite `h` using `[hinv, Matrix.diagonal_map (map_zero _)]`. Use `h using 2 with y` and compare the differences between its conclusion and the goal.

Rewrite using `[LinearMap.funLeft_apply]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Rewrite using `[Matrix.mulVec_diagonal]`. Both sides reduce to the same expression.
-/
theorem dilate_mem_schA {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {a : F} (ha : a ≠ 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : (fun y => Φ (algebraMap F (AF F) a • y)) ∈ schA F κ := by
  classical
  have hdet : IsUnit (Matrix.diagonal fun _ : κ => a⁻¹).det := by
    rw [Matrix.det_diagonal]
    exact (Finset.prod_ne_zero_iff.2 fun _ _ => inv_ne_zero ha).isUnit
  have hinv : (Matrix.diagonal fun _ : κ => a⁻¹)⁻¹ = Matrix.diagonal fun _ : κ => a := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal]
    simp [mul_inv_cancel₀ ha]
  have h := GlobalTheory.SympChangeBij.levi_mapsTo _ hdet Φ hΦ
  rw [hinv, Matrix.diagonal_map (map_zero _)] at h
  convert h using 2 with y
  rw [LinearMap.funLeft_apply]
  congr 1
  funext i
  rw [Matrix.mulVec_diagonal]
  rfl

/- English proof (translation)
Introduce `F _ _ hF ψ hψ κ _ _ _ μ hμ Φ hΦ`. Establish `h0` using `GlobalTheory.SubstIntertw.isStd_stdChar F`. Take `⟨a, ha, hψa⟩` from `GlobalTheory.AdeleCharTwist.exists_mul_eq F _ ψ (GlobalTheory.StdCharFromIsStd.isCharAF h0) hψ`. Establish `h` using `dilate_mem_schA ha (fourier_mem_schA_std F _ h0 κ μ Φ hΦ)`. Use `h using 4 with y x` and compare the differences between its conclusion and the goal.

Rewrite using `[hψa, dotProduct_smul, smul_eq_mul]`.
-/
theorem fourier_mem_schA : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), μ.IsAddHaarMeasure → ∀ Φ ∈ schA F κ, (fun y : κ → AF F => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ) ∈ schA F κ := by
  intro F _ _ hF ψ hψ κ _ _ _ μ hμ Φ hΦ
  have h0 := GlobalTheory.SubstIntertw.isStd_stdChar F
  obtain ⟨a, ha, hψa⟩ := GlobalTheory.AdeleCharTwist.exists_mul_eq F _ ψ (GlobalTheory.StdCharFromIsStd.isCharAF h0) hψ
  have h := dilate_mem_schA ha (fourier_mem_schA_std F _ h0 κ μ Φ hΦ)
  convert h using 4 with y x
  rw [hψa, dotProduct_smul, smul_eq_mul]

end GlobalTheory.AdelicFourierSch
