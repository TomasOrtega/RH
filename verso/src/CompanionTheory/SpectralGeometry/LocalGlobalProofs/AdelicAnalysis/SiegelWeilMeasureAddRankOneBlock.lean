import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteProductMultipliableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGramStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolumeStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CoordinateHaarMeasureStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianOneByOneIsScalarStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdelesLocalRingTotallyRealStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsGramFiberMeasuresStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductLocalDensitiesConvergesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ScalarMultiplicationEulerProductStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalMeasuresOrthogonalSumAlmostAllPlacesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureRankOneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSumStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitProductClosurePropertiesStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TprodComplementSplitFinsetStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryActionConsTupleMeasurableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.PureAdelicFunctionMeasurableStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneEventuallyStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryFiniteSetDecompositionStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Step

/- English proof (translation)
Assume the negation of the conclusion as `hx`. Conclude with `hv (hS (by simpa using hx))`.
-/
theorem of_cofinite {α : Type} {p : α → Prop} (h : ∀ᶠ v in Filter.cofinite, p v) {S : Finset α}
    (hS : (Filter.eventually_cofinite.1 h).toFinset ⊆ S) {v : α} (hv : v ∉ S) : p v := by
  by_contra hx
  exact hv (hS (by simpa using hx))

/- English proof (translation)
Take `⟨h1, h2, h3, h4, -⟩` from `GlobalTheory.T.completion_is_local_ring F v`. Use `haveI := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M`. Conclude with `(((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2).measurableSet`.
-/
theorem lattice_measurable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) : MeasurableSet (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)).2.2.2.2.2.2.2.1 n M
  exact (((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2).measurableSet

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ t ht n d b I minf m hE`. Establish `hLi : IsLocR (Ainf F)` using `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1`. Establish `hLv : ∀ v, IsLocR (Fv F v)` using `GlobalTheory.T.completion_is_local_ring F`. Use `haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩`.

Take `⟨hfin, hsum, S₀, hS₀⟩` from `hE`. Take `⟨S₁, hS₁⟩` from `GlobalTheory.T.adelic_unitary_finite_set_decomposition F E σ hCM M J hJ t ht d b`. Use `⟨S₀ ∪ S₁, fun S hS φinf φ Ψinf Ψ hφinf hφ hΨinf hΨ hG h => ?_⟩` and prove the remaining obligations. Establish `hS0 : S₀ ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `hS1 : S₁ ⊆ S` using `fun x hx => hS (by simp [hx])`.

Take `⟨ginf, g, Sh, hh⟩` from `hS₁ h`. Take `⟨hi, hii⟩` from `hh S hS1`. Establish `hmi : Measurable fun Y : Fin n → Fin M → Ainf F ⊗[F] E => actW (Ainf F) σ _ ginf (consTup Y)` using `GlobalTheory.T.unitary_action_cons_tuple_measurable F E σ hCM (Ainf F) hLi n M _ ginf`. Establish `hmv : ∀ v, Measurable fun Y : Fin n → Fin M → Fv F v ⊗[F] E => actW (Fv F v) σ _ (g v) (consTup Y)` using `fun v => GlobalTheory.T.unitary_action_cons_tuple_measurable F E σ hCM (Fv F v) (hLv v) n M _ (g v)`. Establish `hlatm : ∀ v, MeasurableSet (latV b v : Set (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E))` using `fun v => lattice_measurable σ hCM b (n + 1) (M + 1) v`.

Repeatedly rewrite using `[hi]`. Establish `hmψ : ∀ v, Measurable (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y)))` using `fun v => by`. Distinguish the cases in `hv : v ∈ S`. Simplify using `only [hv, if_true]`. Conclude with `(hφ v).comp (hmv v)`.

Simplify using `only [hv, if_false]`. Conclude with `(measurable_one.indicator (hlatm v)).comp (hmv v)`. Establish `hsplit : ∏ v ∈ S ∪ Sh, ∫⁻ X, (if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup X)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X))) ∂(m v) = (∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ((∏ v ∈ Sh \ S, (latV b v).indic …`. Rewrite using `[Finset.union_comm, ← Finset.sdiff_union_self_eq_union, Finset.prod_union Finset.sdiff_disjoint, mul_comm, ← Finset.prod_mul_distrib]`. Use `congr 1`.

Use `Finset.prod_congr rfl fun v hv => ?_` and prove the remaining obligations. Simplify using `only [hv, if_true]`. Conclude with `(hΨ v (g v)).symm`. Use `Finset.prod_congr rfl fun v hv => ?_` and prove the remaining obligations. Establish `hvS : v ∉ S` using `(Finset.mem_sdiff.1 hv).2`.

Simplify using `only [hvS, if_false]`. Establish `e1 : ∫⁻ X, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X)) ∂(m v) = m v {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v}`. Establish `: (fun X : Fin n → Fin M → Fv F v ⊗[F] E => (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ (g v) (consTup X))) = {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v}.indicator 1`. Use function extensionality and compare the values at `X`. Simplify using `[Set.indicator]`.

Rewrite using `[this]`. Conclude with `lintegral_indicator_one ((hmv v) (hlatm v))`. Rewrite using `[e1, hG v hvS (g v)]`. Simplify using `[Set.indicator]`. Establish `hmφ : Measurable (fun Y : Fin n → Fin M → Ainf F ⊗[F] E => φinf (actW (Ainf F) σ _ ginf (consTup Y)))` using `hφinf.comp hmi`.

Establish `htail` using `GlobalTheory.T.tprod_complement_split_finset (HeightOneSpectrum (𝓞 F)) (fun v => (m v (latV b v)).toReal) S (S ∪ Sh) hsum Finset.subset_union_left`. Rewrite `htail` using `[Finset.union_sdiff_left]`. Establish `hτ : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) = (∏ v ∈ Sh \ S, m v (latV b v)) * ENNReal.ofReal (∏' v : {v // v ∉ S ∪ Sh}, (m v.1 (latV b v.1)).toReal)`. Rewrite using `[htail, ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg), ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]`. Use `congr 1`.

Conclude with `Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (hfin v).ne`. Rewrite using `[hS₀ (S ∪ Sh) (hS0.trans Finset.subset_union_left) _ _ hmφ hmψ, hii, hsplit, hτ, hΨinf ginf]`. Simplify using `only [ENNReal.coe_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem theta_hypothesis : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), IsEulerProd b I 1 minf m → ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₂ ⊆ S → ∀ (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), Measurable φinf → (∀ v, Measurable (φ v)) → (∀ g : HA (Ainf F) σ (blockOne (algebraMap F E t) J), Ψinf (actW (Ainf F) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φinf (actW (Ainf F) σ _ g (consTup X)) ∂minf) → (∀ v, ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J), Ψ v (actW (Fv F v) σ _ g (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ v (actW (Fv F v) σ _ g (consTup X)) ∂(m v)) → (∀ v, v ∉ S → ∀ g : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m v {X | actW (Fv F v) σ _ g (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m v (latV b v)) (actW (Fv F v) σ _ g (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) → ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) * pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) ∂I := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n d b I minf m hE
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  obtain ⟨hfin, hsum, S₀, hS₀⟩ := hE
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.adelic_unitary_finite_set_decomposition F E σ hCM M J hJ t ht d b
  refine ⟨S₀ ∪ S₁, fun S hS φinf φ Ψinf Ψ hφinf hφ hΨinf hΨ hG h => ?_⟩
  have hS0 : S₀ ⊆ S := fun x hx => hS (by simp [hx])
  have hS1 : S₁ ⊆ S := fun x hx => hS (by simp [hx])
  obtain ⟨ginf, g, Sh, hh⟩ := hS₁ h
  obtain ⟨hi, hii⟩ := hh S hS1
  have hmi : Measurable fun Y : Fin n → Fin M → Ainf F ⊗[F] E =>
      actW (Ainf F) σ _ ginf (consTup Y) := GlobalTheory.T.unitary_action_cons_tuple_measurable F E σ hCM (Ainf F) hLi n M _ ginf
  have hmv : ∀ v, Measurable fun Y : Fin n → Fin M → Fv F v ⊗[F] E =>
      actW (Fv F v) σ _ (g v) (consTup Y) := fun v => GlobalTheory.T.unitary_action_cons_tuple_measurable F E σ hCM (Fv F v) (hLv v) n M _ (g v)
  have hlatm : ∀ v, MeasurableSet (latV b v : Set (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E)) := fun v => lattice_measurable σ hCM b (n + 1) (M + 1) v
  simp_rw [hi]
  have hmψ : ∀ v, Measurable (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) := fun v => by
    by_cases hv : v ∈ S
    · simp only [hv, if_true]; exact (hφ v).comp (hmv v)
    · simp only [hv, if_false]; exact (measurable_one.indicator (hlatm v)).comp (hmv v)
  have hsplit : ∏ v ∈ S ∪ Sh, ∫⁻ X, (if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup X)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X))) ∂(m v) =
      (∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) *
        ((∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, m v (latV b v)) := by
    rw [Finset.union_comm, ← Finset.sdiff_union_self_eq_union, Finset.prod_union Finset.sdiff_disjoint, mul_comm, ← Finset.prod_mul_distrib]
    congr 1
    · refine Finset.prod_congr rfl fun v hv => ?_
      simp only [hv, if_true]; exact (hΨ v (g v)).symm
    · refine Finset.prod_congr rfl fun v hv => ?_
      have hvS : v ∉ S := (Finset.mem_sdiff.1 hv).2
      simp only [hvS, if_false]
      have e1 : ∫⁻ X, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup X)) ∂(m v) =
          m v {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v} := by
        have : (fun X : Fin n → Fin M → Fv F v ⊗[F] E => (latV b v).indicator (1 : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (actW (Fv F v) σ _ (g v) (consTup X))) =
            {X | actW (Fv F v) σ _ (g v) (consTup X) ∈ latV b v}.indicator 1 := by
          funext X; simp [Set.indicator]
        rw [this]; exact lintegral_indicator_one ((hmv v) (hlatm v))
      rw [e1, hG v hvS (g v)]
      simp [Set.indicator]
  have hmφ : Measurable (fun Y : Fin n → Fin M → Ainf F ⊗[F] E => φinf (actW (Ainf F) σ _ ginf (consTup Y))) := hφinf.comp hmi
  have htail := GlobalTheory.T.tprod_complement_split_finset (HeightOneSpectrum (𝓞 F)) (fun v => (m v (latV b v)).toReal) S (S ∪ Sh) hsum Finset.subset_union_left
  rw [Finset.union_sdiff_left] at htail
  have hτ : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) = (∏ v ∈ Sh \ S, m v (latV b v)) *
      ENNReal.ofReal (∏' v : {v // v ∉ S ∪ Sh}, (m v.1 (latV b v.1)).toReal) := by
    rw [htail, ENNReal.ofReal_mul (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg),
      ENNReal.ofReal_prod_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)]
    congr 1
    exact Finset.prod_congr rfl fun v _ => ENNReal.ofReal_toReal (hfin v).ne
  rw [hS₀ (S ∪ Sh) (hS0.trans Finset.subset_union_left) _ _ hmφ hmψ, hii, hsplit, hτ, hΨinf ginf]
  simp only [ENNReal.coe_one, one_mul]
  ring

/- English proof (translation)
Establish `hR'` using `hR`. Take `⟨h1, h2, h3, h4, -⟩` from `hR'`. Establish `hh` using `GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam`. Conclude with `GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ R hR n _ _ (hh.2.1 n M) (hh.2.2 n)`.
-/
theorem loc_families {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R]
    (hR : IsLocR R) {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (hlam : lam.IsAddHaarMeasure) (n : ℕ) :
    ∃ m, IsGramFib R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m := by
  have hR' := hR
  obtain ⟨h1, h2, h3, h4, -⟩ := hR'
  have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  exact GlobalTheory.T.exists_gram_fiber_measures F E σ hCM M J hJ R hR n _ _ (hh.2.1 n M) (hh.2.2 n)

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ t ht n hn T hT hdet hT' hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm`. Establish `hLi : IsLocR (Ainf F)` using `GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1`. Establish `hLv : ∀ v, IsLocR (Fv F v)` using `GlobalTheory.T.completion_is_local_ring F`. Use `haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩`.

Establish `hta : algebraMap F E t ≠ 0` using `by simpa using ht`. Take `⟨hdetb, hhermb, -, -⟩` from `GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M J t`. Establish `hJ' : IsHermND σ (blockOne (algebraMap F E t) J)` using `⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩`. Establish `hdet' : (blockOne (algebraMap F E t) T).det ≠ 0`. Rewrite using `[(GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM n T t).1]`.

Conclude with `mul_ne_zero hta hdet`. Take `⟨m₁inf, hm₁inf⟩` from `loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1`. Take `⟨m'inf, hm'inf⟩` from `loc_families σ hCM J hJ (Ainf F) hLi b laminf hinf.1 n`. Use `choose m₁ hm₁ using fun v => loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1`. Use `choose m' hm' using fun v => loc_families σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hlam v).1 n`.

Take `⟨⟨μ₁, hμ₁⟩, hFV⟩` from `GlobalTheory.T.unitary_group_finite_volume F E σ hCM M J hJ`. Take `⟨⟨𝓕₁, h𝓕₁⟩, -⟩` from `hFV μ₁ hμ₁`. Take `⟨cinf, c, hc, hcinf, hcv⟩` from `GlobalTheory.T.scalar_multiplication_euler_product F E σ hCM (algebraMap F E t) hta`. Establish `hKi : (coordK (Ainf F) b laminf).map (fun y => inclR (Ainf F) (algebraMap F E t) * y) = cinf • coordK (Ainf F) b laminf`. Take `⟨h1, h2, h3, h4, -⟩` from `hLi`.

Conclude with `hcinf _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Ainf F) d b laminf hinf.1).1`. Establish `hKv : ∀ v, (coordK (Fv F v) b (lam v)).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c v • coordK (Fv F v) b (lam v)` using `fun v => by`. Take `⟨h1, h2, h3, h4, -⟩` from `hLv v`. Conclude with `hcv v _ (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1).1`. Take `⟨-, -, -, -, -, -, -, S₃, hS₃⟩` from `GlobalTheory.T.unit_product_closure_properties F cinf 1 c (fun _ => 1) hc ⟨by simp, by simp⟩`.

Establish `hE'` using `hSW d b laminf lam hinf hlam μ₁ 𝓕₁ hμ₁ h𝓕₁ m'inf (fun v => m' v) hm'inf hm'`. Set `T1 : Matrix (Fin 1) (Fin 1) E` to `fun _ _ => algebraMap F E t`. Establish `hT1 : ∀ a b, σ (T1 b a) = T1 a b` using `fun a b => by simp [T1]`. Establish `hdet1 : T1.det ≠ 0` using `by rw [Matrix.det_fin_one]; exact hta`. Establish `hE₁` using `GlobalTheory.T.siegel_weil_measure_rank_one F E σ hCM (M + 1) _ hJ' (by omega) T1 hT1 hdet1 d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 m₁inf m₁ hm₁inf hm₁`.

Take `⟨β, hβ1, -, hβ2⟩` from `GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hCM T1 hT1`. Establish `hβ : β = t` using `(algebraMap F E).injective (congrFun (congrFun hβ1 0) 0).symm`. Rewrite `hβ2` using `[hβ]`. Simplify using `only [hβ2] at hE₁`. Take `⟨-, hsum₁, S₁, hS₁⟩` from `hE₁`.

Establish `hsum'` using `hE'.2.1`. Establish `hgood` using `GlobalTheory.T.euler_product_local_densities_converges F E σ hCM (M + 1) _ hJ' (n + 1) (Or.inr (by omega)) _ hT' hdet' d b lam hlam m hm`. Use `⟨hgood.1, hgood.2, ?_⟩` and prove the remaining obligations. Take `⟨S₂, hS₂⟩` from `theta_hypothesis F E σ hCM M J hJ t ht n d b _ _ _ hE'`. Establish `hG` using `GlobalTheory.T.local_density_block_one_eventually F E σ hCM M J hJ t ht n T hT hdet hT' d b`.

Establish `hSG` using `GlobalTheory.T.local_measures_orthogonal_sum_almost_all_places F E σ hCM M J hJ t ht n T hT hdet d b`. Use `⟨S₁ ∪ S₂ ∪ S₃ ∪ (Filter.eventually_cofinite.1 hG).toFinset ∪ (Filter.eventually_cofinite.1 hSG).toFinset, fun S hS φinf φ hφinf hφ => ?_⟩` and prove the remaining obligations. Establish `hS1 : S₁ ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `hS2 : S₂ ⊆ S` using `fun x hx => hS (by simp [hx])`. Establish `hS3 : S₃ ⊆ S` using `fun x hx => hS (by simp [hx])`.

Establish `hS4 : (Filter.eventually_cofinite.1 hG).toFinset ⊆ S` using `fun x hx => hS (by`. Simplify using `only [Finset.mem_union]`. Conclude with `Or.inl (Or.inr hx))`. Establish `hS5 : (Filter.eventually_cofinite.1 hSG).toFinset ⊆ S` using `fun x hx => hS (by`. Simplify using `only [Finset.mem_union]`.

Conclude with `Or.inr hx)`. Take `⟨hc1, hc2⟩` from `hS₃ S hS3`. Take `⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩` from `GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Ainf F) hLi d b laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf`. Use `choose Ψ hΨm hΨ1 hΨ2 using fun v => GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Fv F v) (hLv v) d b (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (φ v) (hφ v)`. Establish `hHv : ∀ v, (coordW (Fv F v) b (lam v) n M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) n).IsAddHaarMeasure` using `fun v => by`.

Take `⟨h1, h2, h3, h4, -⟩` from `hLv v`. Establish `hh` using `GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1`. Conclude with `⟨hh.2.1 n M, hh.2.2 n⟩`. Establish `hHyp` using `hS₂ S hS2 φinf φ Ψinf Ψ hφinf hφ hΨinf1 hΨ1 (fun v hv g => of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g)`. Use `set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) with hτ'`.

Establish `hPm : Measurable (pureL b S Ψinf Ψ)` using `GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b 1 (M + 1) S Ψinf Ψ hΨinfm hΨm`. Establish `hth` using `GlobalTheory.T.lintegral_thetaMeas_block_one_eq_rank_one F E σ hCM M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ) (fun y => τ' * pureL b S Ψinf Ψ y) (GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b (n + 1) (M + 1) S φinf φ hφinf hφ) (hPm.const_mul τ') hHy …`. Establish `hone` using `hS₁ S hS1 Ψinf Ψ hΨinfm hΨm`. Rewrite using `[hth, lintegral_const_mul _ hPm]`. Establish `hone' : ∫⁻ X, pureL b S Ψinf Ψ X ∂(thetaMeas σ _ μ 𝓕 {y : Fin 1 → Fin (M + 1) → E | gramE σ (blockOne (algebraMap F E t) J) y = fun _ _ => algebraMap F E t}) = _` using `hone`.

Rewrite using `[hone']`. Establish `hprod : (∫⁻ X, φinf X ∂(minf (hermOf (Ainf F) σ _ hT'))) * ∏ v ∈ S, ∫⁻ X, φ v X ∂(m v (hermOf (Fv F v) σ _ hT')) = (∫⁻ y, Ψinf y ∂(m₁inf (hermScal (Ainf F) σ (algebraMap F (Ainf F) t)))) * ∏ v ∈ S, ∫⁻ y, Ψ v y ∂(m₁ v (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)))`. Establish `hone2 : (cinf : ℝ≥0∞) * ∏ v ∈ S, (c v : ℝ≥0∞) = 1` using `by exact_mod_cast hc2`. Rewrite using `[hΨinf2, Finset.prod_congr rfl (fun v _ => hΨ2 v), Finset.prod_mul_distrib, Finset.prod_pow]`. Combine the equalities or inequalities in the displayed calculation.

Establish `htail : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal) = τ' * ENNReal.ofReal (∏' v : {v // v ∉ S}, (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal)`. Establish `hA` using `GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) (hsum'.subtype _)`. Establish `hB` using `GlobalTheory.T.infinite_product_multipliable {v // v ∉ S} (fun v => (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal) (hsum₁.subtype _)`. Establish `hcong : ∀ v : {v // v ∉ S}, (m v.1 (hermOf (Fv F v.1) σ _ hT') (latV b v.1)).toReal = (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal * (m₁ v.1 (hermScal (Fv F v.1) σ (algebraMap F (Fv F v.1) t)) (latV b v.1)).toReal` using `fun v => by`. Rewrite using `[of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]`.

Simplify using `[ENNReal.toReal_mul]`. Rewrite using `[tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]`. Rewrite using `[hprod, htail]`. Simplify using `only [ENNReal.coe_one, one_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem blockOne_step : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ n : ℕ, n + 2 ≤ M → ∀ (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), SWMeas σ J T hT → SWMeas σ (blockOne (algebraMap F E t) J) (blockOne (algebraMap F E t) T) hT' := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n hn T hT hdet hT' hSW d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  classical
  have hLi : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := GlobalTheory.T.completion_is_local_ring F
  haveI hBi : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI hBv : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  have hta : algebraMap F E t ≠ 0 := by simpa using ht
  obtain ⟨hdetb, hhermb, -, -⟩ := GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hhermb hJ.1, by rw [hdetb]; exact mul_ne_zero hta hJ.2⟩
  have hdet' : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [(GlobalTheory.T.block_one_det_hermitian_gram F E σ hCM n T t).1]; exact mul_ne_zero hta hdet

  obtain ⟨m₁inf, hm₁inf⟩ := loc_families σ hCM _ hJ' (Ainf F) hLi b laminf hinf.1 1
  obtain ⟨m'inf, hm'inf⟩ := loc_families σ hCM J hJ (Ainf F) hLi b laminf hinf.1 n
  choose m₁ hm₁ using fun v => loc_families σ hCM _ hJ' (Fv F v) (hLv v) b (lam v) (hlam v).1 1
  choose m' hm' using fun v => loc_families σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hlam v).1 n
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
  have hgood := GlobalTheory.T.euler_product_local_densities_converges F E σ hCM (M + 1) _ hJ' (n + 1) (Or.inr (by omega)) _ hT' hdet' d b lam hlam m hm
  refine ⟨hgood.1, hgood.2, ?_⟩
  obtain ⟨S₂, hS₂⟩ := theta_hypothesis F E σ hCM M J hJ t ht n d b _ _ _ hE'
  have hG := GlobalTheory.T.local_density_block_one_eventually F E σ hCM M J hJ t ht n T hT hdet hT' d b
  have hSG := GlobalTheory.T.local_measures_orthogonal_sum_almost_all_places F E σ hCM M J hJ t ht n T hT hdet d b
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
  obtain ⟨Ψinf, hΨinfm, hΨinf1, hΨinf2⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Ainf F) hLi d b
    laminf hinf.1 minf m₁inf m'inf hminf hm₁inf hm'inf cinf hKi φinf hφinf
  choose Ψ hΨm hΨ1 hΨ2 using fun v => GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Fv F v) (hLv v) d b
    (lam v) (hlam v).1 (m v) (m₁ v) (m' v) (hm v) (hm₁ v) (hm' v) (c v) (hKv v) (φ v) (hφ v)
  have hHv : ∀ v, (coordW (Fv F v) b (lam v) n M).IsAddHaarMeasure ∧ (coordHerm (Fv F v) σ b (lam v) n).IsAddHaarMeasure := fun v => by
    obtain ⟨h1, h2, h3, h4, -⟩ := hLv v
    have hh := GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b (lam v) (hlam v).1
    exact ⟨hh.2.1 n M, hh.2.2 n⟩
  have hHyp := hS₂ S hS2 φinf φ Ψinf Ψ hφinf hφ hΨinf1 hΨ1 (fun v hv g =>
    of_cofinite hSG hS5 hv _ _ (m' v) (hHv v).1 (hHv v).2 (hm' v) g)
  set τ' := ENNReal.ofReal (∏' v : {v // v ∉ S}, (m' v.1 (hermOf (Fv F v.1) σ T hT) (latV b v.1)).toReal) with hτ'
  have hPm : Measurable (pureL b S Ψinf Ψ) := GlobalTheory.T.pure_adelic_function_measurable F E σ hCM d b 1 (M + 1) S Ψinf Ψ hΨinfm hΨm
  have hth := GlobalTheory.T.lintegral_thetaMeas_block_one_eq_rank_one F E σ hCM M J hJ t ht n T μ 𝓕 hμ h𝓕 μ₁ 𝓕₁ hμ₁ h𝓕₁ (pureL b S φinf φ)
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
      rw [of_cofinite hG hS4 v.2 (lam v.1) (hlam v.1).1 (m v.1) (m₁ v.1) (m' v.1) (hm v.1) (hm₁ v.1) (hm' v.1) (c v.1) (hKv v.1), hc1 v.1 v.2]
      simp [ENNReal.toReal_mul]
    rw [tprod_congr hcong, hA.1.tprod_mul hB.1, ENNReal.ofReal_mul (hA.2.2.2 fun _ => ENNReal.toReal_nonneg)]
  rw [hprod, htail]
  simp only [ENNReal.coe_one, one_mul]
  ring

end GlobalTheory.CompanionTheory.SW.Step
