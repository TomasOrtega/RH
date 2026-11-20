import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureAddRankOneBlock
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureExtensionByScalarStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilProductOfLocalIdentitiesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeUnramifiedAlmostAllStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreMeasureStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreIntegralStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section
namespace GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso

/- English proof (translation)
Establish `hB : BorelSpace (Ainf F)` using `⟨rfl⟩`. Take `⟨-, hW, hH⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) _ b lam hlam`. Conclude with `GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hCM M n J hJ _ _ (hW n M) (hH n)`.
-/
theorem free_inf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure (Ainf F)) (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ m, IsGramFibFree (Ainf F) σ J n (coordW (Ainf F) b lam n M) (coordHerm (Ainf F) σ b lam n) m := by
  have hB : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) _ b lam hlam
  exact GlobalTheory.T.exists_fibreMeasures_archimedeanGramMap F E σ hCM M n J hJ _ _ (hW n M) (hH n)

/- English proof (translation)
Use `PI.VolStabS.secondCountable_Fv F v` as an intermediate fact. Use `PI.VolStabS.locallyCompact_Fv F v` as an intermediate fact. Establish `hB : BorelSpace (Fv F v)` using `⟨rfl⟩`. Take `⟨-, hW, hH⟩` from `GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) _ b lam hlam`. Conclude with `PI.OmFibreUniq.W.gram_map_fibre_existence σ J v n hCM hJ _ _ (hW n M) (hH n)`.
-/
theorem free_v {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v))
    (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ m, IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m := by
  have := PI.VolStabS.secondCountable_Fv F v
  have := PI.VolStabS.locallyCompact_Fv F v
  have hB : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) _ b lam hlam
  exact PI.OmFibreUniq.W.gram_map_fibre_existence σ J v n hCM hJ _ _ (hW n M) (hH n)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hT' d b`. Take `⟨hdet, hherm, -, -⟩` from `BlockAlg.block_alg F E σ hCM M J t`. Establish `hND : IsHermND σ (blockOne (algebraMap F E t) J)` using `⟨hherm hJ.1, by`. Rewrite using `[hdet]`. Conclude with `mul_ne_zero (by simpa using ht) hJ.2⟩`.

Use `filter_upwards [GlobalTheory.T.local_volume_unramified_almost_all F E σ hCM M J hJ t ht n T hT d b] with v hv`. Introduce `lam hlam m m₁ m' hm hm₁ hm' c hc`. Establish `hLoc` using `LocFv.isLocR_Fv F v`. Take `⟨i1, i2, i3, i4, i5, i6, -⟩` from `id hLoc`. Establish `: BorelSpace (Fv F v)` using `⟨rfl⟩`.

Establish `hH` using `coord_measures_haar F E σ hCM (Fv F v) d b lam hlam`. Take `⟨hring, -, -, -, -, -, -, hB, -, -⟩` from `TopK.topTens_props F E σ hCM (Fv F v)`. Establish `hlat : ∀ n' M' : ℕ, MeasurableSet (latV b v : Set (Fin n' → Fin M' → Fv F v ⊗[F] E))`. Introduce `n' M'`. Use `haveI := hB n' M'`.

Conclude with `((MeasProj.proj_props F E σ hCM d b n' M').2.2.2.1 v).2.measurableSet`. Take `⟨Ψ, -, hΨ, hint⟩` from `GlobalTheory.T.scalar_extension_fibre_measure F E σ hCM M J hJ t ht n T hT hT' (Fv F v) hLoc d b lam hlam m m₁ m' hm hm₁ hm' c hc ((latV b v).indicator 1) (measurable_one.indicator (hlat _ _))`. Use `set A := m' (hermOf (Fv F v) σ T hT) (latV b v) with hA`. Establish `hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))] (latV b v).indicator (fun _ => A)` using `by filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))] with y hy`. Take `⟨hy1, hy2⟩` from `hy`.

Establish `hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) = gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y` using `(StageGood.gram_first (Fv F v) σ J t).trans hy1.symm`. Take `⟨h, rfl⟩` from `GlobalTheory.T.witt_extension_artinian_ring F E σ hCM (M + 1) _ hND (Fv F v) 1 _ y hg (by rw [hg]; exact hy2)`. Rewrite using `[hΨ h]`. Use `haveI := hB n M`. Use `haveI := hB (n + 1) (M + 1)`.

Establish `hS : MeasurableSet {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v}` using `(GoodMass.continuous_act_consTup (Fv F v) hring σ _ h).measurable (hlat _ _)`. Establish `hfun : (fun X : Fin n → Fin M → Fv F v ⊗[F] E => (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ h (consTup X))) = {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v}.indicator 1`. Use function extensionality and compare the values at `X`. Both sides reduce to the same expression. Rewrite using `[hfun, lintegral_indicator_one hS, hv _ _ m' (hH.2.1 n M) (hH.2.2 n) hm' h]`.

Rewrite using `[← lintegral_indicator_one (hlat _ _), hint, lintegral_congr_ae hae, lintegral_indicator_const (hlat _ _)]`.
-/
theorem good_mass_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFibFree (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ c : ℝ≥0, (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c • coordK (Fv F v) b lam → m (hermOf (Fv F v) σ _ hT') (latV b v) = (c : ℝ≥0∞) ^ n * (m' (hermOf (Fv F v) σ T hT) (latV b v) * m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hT' d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [GlobalTheory.T.local_volume_unramified_almost_all F E σ hCM M J hJ t ht n T hT d b] with v hv
  intro lam hlam m m₁ m' hm hm₁ hm' c hc
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, i5, i6, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  have hH := coord_measures_haar F E σ hCM (Fv F v) d b lam hlam
  obtain ⟨hring, -, -, -, -, -, -, hB, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have hlat : ∀ n' M' : ℕ, MeasurableSet (latV b v : Set (Fin n' → Fin M' → Fv F v ⊗[F] E)) := by
    intro n' M'
    haveI := hB n' M'
    exact ((MeasProj.proj_props F E σ hCM d b n' M').2.2.2.1 v).2.measurableSet
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.scalar_extension_fibre_measure F E σ hCM M J hJ t ht n T hT hT' (Fv F v) hLoc d b lam hlam
    m m₁ m' hm hm₁ hm' c hc ((latV b v).indicator 1) (measurable_one.indicator (hlat _ _))
  set A := m' (hermOf (Fv F v) σ T hT) (latV b v) with hA
  have hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))] (latV b v).indicator (fun _ => A) := by
    filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))] with y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) =
        gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y :=
      (StageGood.gram_first (Fv F v) σ J t).trans hy1.symm
    obtain ⟨h, rfl⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hCM (M + 1) _ hND (Fv F v) 1 _ y hg
      (by rw [hg]; exact hy2)
    rw [hΨ h]
    haveI := hB n M
    haveI := hB (n + 1) (M + 1)
    have hS : MeasurableSet {X : Fin n → Fin M → Fv F v ⊗[F] E |
        actW (Fv F v) σ _ h (consTup X) ∈ latV b v} :=
      (GoodMass.continuous_act_consTup (Fv F v) hring σ _ h).measurable (hlat _ _)
    have hfun : (fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
        (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ h (consTup X))) =
        {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v}.indicator 1 := by
      funext X
      rfl
    rw [hfun, lintegral_indicator_one hS, hv _ _ m' (hH.2.1 n M) (hH.2.2 n) hm' h]
  rw [← lintegral_indicator_one (hlat _ _), hint, lintegral_congr_ae hae,
    lintegral_indicator_const (hlat _ _)]

/- English proof (translation)
Establish `ht : ∀ᶠ i in Filter.cofinite, |y i - 1| < 1`. Use `hy.tendsto_cofinite_zero` as an intermediate fact. Conclude with `this.eventually (gt_mem_nhds one_pos)`. Use `Summable.of_norm_bounded_eventually (g := fun i => 2 * |x i - 1| + |y i - 1|) ((hx.mul_left 2).add hy) ?_` and prove the remaining obligations. Use `filter_upwards [ht] with i hi`.

Establish `e : x i * y i - 1 = (x i - 1) * (y i - 1) + (x i - 1) + (y i - 1)` using `by ring`. Rewrite using `[Real.norm_eq_abs, abs_abs, e]`. Establish `h1 : |(x i - 1) * (y i - 1)| ≤ |x i - 1|`. Rewrite using `[abs_mul]`. Conclude with `mul_le_of_le_one_right (abs_nonneg _) hi.le`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem summable_mul_sub_one {ι : Type} {x y : ι → ℝ} (hx : Summable fun i => |x i - 1|)
    (hy : Summable fun i => |y i - 1|) : Summable fun i => |x i * y i - 1| := by
  have ht : ∀ᶠ i in Filter.cofinite, |y i - 1| < 1 := by
    have := hy.tendsto_cofinite_zero
    exact this.eventually (gt_mem_nhds one_pos)
  refine Summable.of_norm_bounded_eventually (g := fun i => 2 * |x i - 1| + |y i - 1|)
    ((hx.mul_left 2).add hy) ?_
  filter_upwards [ht] with i hi
  have e : x i * y i - 1 = (x i - 1) * (y i - 1) + (x i - 1) + (y i - 1) := by ring
  rw [Real.norm_eq_abs, abs_abs, e]
  have h1 : |(x i - 1) * (y i - 1)| ≤ |x i - 1| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hi.le
  calc _ ≤ |(x i - 1) * (y i - 1) + (x i - 1)| + |y i - 1| := abs_add_le _ _
    _ ≤ |(x i - 1) * (y i - 1)| + |x i - 1| + |y i - 1| := by gcongr; exact abs_add_le _ _
    _ ≤ 2 * |x i - 1| + |y i - 1| := by linarith

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ t ht n hn T hT hT' _ hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm`. Establish `hLi : IsLocR (Ainf F)` using `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1`. Establish `hLv : ∀ v, IsLocR (Fv F v)` using `GlobalTheory.T.completion_is_local_ring F`. Use `haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩`.

Establish `hta : algebraMap F E t ≠ 0` using `by simpa using ht`. Take `⟨hdetb, hhermb, -, -⟩` from `GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M J t`. Establish `hJ' : IsHermND σ (blockOne (algebraMap F E t) J)` using `⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩`. Take `⟨m₁inf, hm₁inf⟩` from `Step.loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1`. Take `⟨m'inf, hm'inf⟩` from `free_inf σ hCM J hJ b laminf hinf.1 n`.

Use `choose m₁ hm₁ using fun v => Step.loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1`. Use `choose m' hm' using fun v => free_v σ hCM J hJ b v (lam v) (hlam v).1 n`. Take `⟨⟨μ₁, hμ₁⟩, hFV⟩` from `GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ`. Take `⟨⟨𝓕₁, h𝓕₁⟩, -⟩` from `hFV μ₁ hμ₁`. Take `⟨cinf, c, hc, hcinf, hcv⟩` from `GlobalTheory.T.scalar_multiplication_euler_product F E σ hCM (algebraMap F E t) hta`.

Establish `hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) = cinf • coordK (Ainf F) b laminf`. Take `⟨h1, h2, h3, h4, -⟩` from `hLi`. Conclude with `hcinf _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1).1`. Establish `hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c v • coordK (Fv F v) b (lam v)` using `fun v => by`. Take `⟨h1, h2, h3, h4, -⟩` from `hLv v`.

Conclude with `hcv v _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1`. Take `⟨-, -, -, -, -, -, -, S₃, hS₃⟩` from `GlobalTheory.T.unit_product_closure_properties F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩`. Establish `hE'` using `hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf (fun v => m' v) hm'inf hm'`. Set `T1 : Matrix (Fin 1) (Fin 1) E` to `fun _ _ => algebraMap F E t`. Establish `hT1 : ∀ a b, σ (T1 b a) = T1 a b` using `fun a b => by simp [T1]`.

Establish `hdet1 : T1.det ≠ 0` using `by rw [Matrix.det_fin_one]; exact hta`. Establish `hE₁` using `GlobalTheory.T.siegel_weil_measure_rank_one F E σ hCM (M + 1) _ hJ' (by omega) T1 hT1 hdet1 d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 m₁inf m₁ hm₁inf hm₁`. Take `⟨β, hβ1, -, hβ2⟩` from `GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hCM T1 hT1`. Establish `hβ : β = t` using `(algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm`. Rewrite `hβ2` using `[hβ]`.

Simplify using `only [hβ2] at hE₁`. Take `⟨-, hsum₁, S₁, hS₁⟩` from `hE₁`. Establish `hsum'` using `hE'.2.1`. Establish `hG` using `good_mass_free F E σ hCM M J hJ t ht n T hT hT' d b`. Establish `hgood₁ : ∀ v, m v (hermOf (Fv F v) σ _ hT') (latV b v) < ⊤` using `fun v => GlobalTheory.T.scalar_extension_fibre_integral F E σ hCM M J hJ t ht n T hT hT' (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (GlobalTheory.T.siegel_weil_product_of_local_identities F E σ hCM M J hJ n T hT hSW d b laminf …`.

Establish `hgood₂ : Summable fun v => |(m v (hermOf (Fv F v) σ _ hT') (latV b v)).toReal - 1|`. Establish `hP` using `summable_mul_sub_one hsum' hsum₁`. Use `(summable_congr_cofinite ?_).1 hP` and prove the remaining obligations. Use `filter_upwards [hG, hc.1] with v hv hcv1`. Rewrite using `[hv (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v), hcv1]`.

Simplify using `[ENNReal.toReal_mul]`. Use `⟨hgood₁, hgood₂, ?_⟩` and prove the remaining obligations. Take `⟨S₂, hS₂⟩` from `Step.theta_hypothesis F E σ hCM M J hJ t ht n d b _ _ _ hE'`. Establish `hSG` using `GlobalTheory.T.local_volume_unramified_almost_all F E σ hCM M J hJ t ht n T hT d b`. Use `⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset, fun S hS φinf φ hφinf hφ => ?_⟩` and prove the remaining obligations.

Establish `hS1 : S₁ ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `hS2 : S₂ ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `hS3 : S₃ ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S` using `fun x hx => hS (by`. Simplify using `only [Finset.mem_union]`.

Conclude with `Or.inl (Or.inr hx))`. Establish `hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S` using `fun x hx => hS (by`. Simplify using `only [Finset.mem_union]`. Conclude with `Or.inr hx)`. Take `⟨hc1, hc2⟩` from `hS₃ S hS3`.

Take `⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩` from `GlobalTheory.T.scalar_extension_fibre_measure F E σ hCM M J hJ t ht n T hT hT' (Ainf F) hLi d b laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf`. Use `choose Ψ hΨm hΨ1 hΨ2 using fun v => GlobalTheory.T.scalar_extension_fibre_measure F E σ hCM M J hJ t ht n T hT hT' (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (φ v) (hφ v)`. Establish `hHv : ∀ v, (coordW (Fv F v) b (lam v) n M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) n).IsAddHaarMeasure` using `fun v => by`. Take `⟨h1, h2, h3, h4, -⟩` from `hLv v`. Establish `hh` using `GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1`.

Conclude with `⟨hh.2.1 n M, hh.2.2 n⟩`. Establish `hHyp` using `hS₂ S hS2 φinf φ Ψinf Ψ hφinf hφ hΨinf1 hΨ1 (fun v hv g => Step.of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g)`. Use `set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) with hτ'`. Establish `hPm : Measurable (pureL b S Ψinf Ψ)` using `GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b 1 (M + 1) S Ψinf Ψ hΨinfm hΨm`. Establish `hth` using `GlobalTheory.T.theta_measure_extension_by_scalar F E σ hCM M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ) (fun y => τ' * pureL b S Ψinf Ψ y) (GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (n + 1) (M + 1) S φinf φ hφinf hφ) (hPm.const_mul τ') hHyp`.

Establish `hone` using `hS₁ S hS1 Ψinf Ψ hΨinfm hΨm`. Rewrite using `[hth, lintegral_const_mul _ hPm]`. Establish `hone' : ∫⁻ X, pureL b S Ψinf Ψ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _` using `hone`. Rewrite using `[hone']`. Establish `hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ _ hT')) = (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))`.

Establish `hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1` using `by exact_mod_cast hc2`. Rewrite using `[hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]`. Combine the equalities or inequalities in the displayed calculation. Establish `htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal) = τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)`. Establish `hA` using `GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) (hsum'.subtype _)`.

Establish `hB` using `GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) (hsum₁.subtype _)`. Establish `hcong : ∀ v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal = (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal * (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal` using `fun v => by`. Rewrite using `[Step.of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]`. Simplify using `[ENNReal.toReal_mul]`. Rewrite using `[tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]`.

Rewrite using `[hprod, htail]`. Simplify using `only [ENNReal.coe_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem aniso_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, 2 * n + 1 < M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), (framesE σ J T).Nonempty → SWFree σ J T hT → SWFree σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n hn T hT hT' _ hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hta : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨hdetb, hhermb, -, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩

  obtain ⟨m₁inf, hm₁inf⟩ := Step.loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1
  obtain ⟨m'inf, hm'inf⟩ := free_inf σ hCM J hJ b laminf hinf.1 n
  choose m₁ hm₁ using fun v => Step.loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1
  choose m' hm' using fun v => free_v σ hCM J hJ b v (lam v) (hlam v).1 n
  obtain ⟨⟨μ₁, hμ₁⟩, hFV⟩ := GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ
  obtain ⟨⟨𝓕₁, h𝓕₁⟩, -⟩ := hFV μ₁ hμ₁

  obtain ⟨cinf, c, hc, hcinf, hcv⟩ := GlobalTheory.T.scalar_multiplication_euler_product F E σ hCM (algebraMap F E t) hta
  have hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) =
      cinf • coordK (Ainf F) b laminf := by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLi
    exact hcinf _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1).1
  have hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      c v • coordK (Fv F v) b (lam v) := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    exact hcv v _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1
  obtain ⟨-, -, -, -, -, -, -, S₃, hS₃⟩ := GlobalTheory.T.unit_product_closure_properties F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩

  have hE' := hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf (fun v => m' v) hm'inf hm'
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun a b => by simp [T1]
  have hdet1 : T1.det ≠ 0 := by rw [Matrix.det_fin_one]; exact hta
  have hE₁ := GlobalTheory.T.siegel_weil_measure_rank_one F E σ hCM (M + 1) _ hJ' (by omega) T1 hT1 hdet1 d b laminf lam hinf hlam μ 𝓕 hμ h𝓕
    m₁inf m₁ hm₁inf hm₁
  obtain ⟨β, hβ1, -, hβ2⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hCM T1 hT1
  have hβ : β = t := (algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm
  rw [hβ] at hβ2
  simp only [hβ2] at hE₁
  obtain ⟨-, hsum₁, S₁, hS₁⟩ := hE₁
  have hsum' := hE'.2.1
  have hG := good_mass_free F E σ hCM M J hJ t ht n T hT hT' d b
  have hgood₁ : ∀ v, m v (hermOf (Fv F v) σ _ hT') (latV b v) < ⊤ := fun v =>
    GlobalTheory.T.scalar_extension_fibre_integral F E σ hCM M J hJ t ht n T hT hT' (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v)
      (hm v) (hm₁ v) (hm' v) (c v) (hKv v)
      (GlobalTheory.T.siegel_weil_product_of_local_identities F E σ hCM M J hJ n T hT hSW d b laminf lam hinf hlam v (m' v) (hm' v)) _
      ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b (n + 1) (M + 1)).2.2.2.1 v).1
  have hgood₂ : Summable fun v => |(m v (hermOf (Fv F v) σ _ hT') (latV b v)).toReal - 1| := by
    have hP := summable_mul_sub_one hsum' hsum₁
    refine (summable_congr_cofinite ?_).1 hP
    filter_upwards [hG, hc.1] with v hv hcv1
    rw [hv (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v), hcv1]
    simp [ENNReal.toReal_mul]
  refine ⟨hgood₁, hgood₂, ?_⟩
  obtain ⟨S₂, hS₂⟩ := Step.theta_hypothesis F E σ hCM M J hJ t ht n d b _ _ _ hE'
  have hSG := GlobalTheory.T.local_volume_unramified_almost_all F E σ hCM M J hJ t ht n T hT d b
  refine ⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset,
    fun S hS φinf φ hφinf hφ => ?_⟩
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  have hS2 : S₂ ⊆ S := fun x hx => hS (by simp [hx])
  have hS3 : S₃ ⊆ S := fun x hx => hS (by simp [hx])
  have hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inl (Or.inr hx))
  have hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S := fun x hx => hS (by
    simp only [Finset.mem_union]; exact Or.inr hx)
  obtain ⟨hc1, hc2⟩ := hS₃ S hS3
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := GlobalTheory.T.scalar_extension_fibre_measure F E σ hCM M J hJ t ht n T hT hT' (Ainf F) hLi d b
    laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf
  choose Ψ hΨm hΨ1 hΨ2 using fun v => GlobalTheory.T.scalar_extension_fibre_measure F E σ hCM M J hJ t ht n T hT hT' (Fv F v) (hLv v) d b
    (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (φ v) (hφ v)
  have hHv : ∀ v, (coordW (Fv F v) b (lam v) n M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) n).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact ⟨hh.2.1 n M, hh.2.2 n⟩
  have hHyp := hS₂ S hS2 φinf φ Ψinf Ψ hφinf hφ hΨinf1 hΨ1 (fun v hv g =>
    Step.of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g)
  set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) with hτ'
  have hPm : Measurable (pureL b S Ψinf Ψ) := GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b 1 (M + 1) S Ψinf Ψ hΨinfm hΨm
  have hth := GlobalTheory.T.theta_measure_extension_by_scalar F E σ hCM M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ)
    (fun y => τ' * pureL b S Ψinf Ψ y) (GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (n + 1) (M + 1) S φinf φ hφinf hφ)
    (hPm.const_mul τ') hHyp
  have hone := hS₁ S hS1 Ψinf Ψ hΨinfm hΨm
  rw [hth, lintegral_const_mul _ hPm]
  have hone' : ∫⁻ X, pureL b S Ψinf Ψ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _ := hone
  rw [hone']
  have hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ _ hT')) =
      (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t))) := by
    have hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1 := by exact_mod_cast hc2
    rw [hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]
    calc _ = ((cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞)) ^ n * ((∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) *
        ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))) := by rw [mul_pow]; ring
      _ = _ := by rw [hone2, one_pow, one_mul]
  have htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal) =
      τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) := by
    have hA := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal)
      (hsum'.subtype _)
    have hB := GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)
      (hsum₁.subtype _)
    have hcong : ∀ v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal =
        (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal * (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal := fun v => by
      rw [Step.of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]
      simp [ENNReal.toReal_mul]
    rw [tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]
  rw [hprod, htail]
  simp only [ENNReal.coe_one, one_mul]
  ring

end GlobalTheory.CompanionTheory.WeilSiegel.Free.Aniso
