import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.StageData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerateStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramFiberMeasureGeneralRankExtensionStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompactStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology ProbabilityTheory
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

/- English proof (translation)
Establish `hmeas : Measurable fun a => η a Set.univ` using `η.measurable_coe MeasurableSet.univ`. Set `g : α → ℕ` to `fun a => ⌊(η a Set.univ).toReal⌋₊`. Establish `hg : Measurable g` using `Nat.measurable_floor.comp hmeas.ennreal_toReal`. Establish `hB : ∀ j : ℕ, MeasurableSet (g ⁻¹' {j})` using `fun j => hg (measurableSet_singleton j)`. Set `ηs : ℕ → Kernel α β` to `fun j => Kernel.piecewise (hB j) η 0`.

Establish `hfin : ∀ j, IsFiniteKernel (ηs j)`. Introduce `j`. Use `⟨⟨(j : ℝ≥0∞) + 1, by simp [ENNReal.add_lt_top], fun a => ?_⟩⟩` and prove the remaining obligations. Distinguish the cases in `ha : a ∈ g ⁻¹' {j}`. Establish `hj : g a = j` using `ha`.

Establish `h1 : (η a Set.univ).toReal < (j : ℝ) + 1`. Use `Nat.lt_floor_add_one (η a Set.univ).toReal` as an intermediate fact. Simplify `this` using `[g, hj]`. Establish `h2 : η a Set.univ = ENNReal.ofReal (η a Set.univ).toReal` using `(ENNReal.ofReal_toReal (h a).ne).symm`. Simplify using `only [ηs, Kernel.piecewise_apply, if_pos ha]`.

Rewrite using `[h2]`. Use `ENNReal.ofReal_le_of_le_toReal ?_` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_add (by simp) (by simp)]`. Simplify using `using h1.le`. Establish `ha' : ¬ g a = j` using `ha`.

Simplify using `[ηs, Kernel.piecewise_apply, ha']`. Establish `hsum : η = Kernel.sum ηs`. Use extensionality with `a s hs`. Rewrite using `[Kernel.sum_apply, Measure.sum_apply _ hs, tsum_eq_single (g a)]`. Simplify using `[ηs, Kernel.piecewise_apply]`.

Introduce `j hj`. Establish `ha' : ¬ g a = j` using `fun h' => hj h'.symm`. Simplify using `[ηs, Kernel.piecewise_apply, ha']`. Rewrite using `[hsum]`. Conclude with `⟨⟨fun j => ηs j, hfin, rfl⟩⟩`.
-/
theorem isSFiniteKernel_of_forall_univ_lt_top {α β : Type} [MeasurableSpace α] [MeasurableSpace β]
    (η : Kernel α β) (h : ∀ a, η a Set.univ < ⊤) : IsSFiniteKernel η := by
  classical
  have hmeas : Measurable fun a => η a Set.univ := η.measurable_coe MeasurableSet.univ
  let g : α → ℕ := fun a => ⌊(η a Set.univ).toReal⌋₊
  have hg : Measurable g := Nat.measurable_floor.comp hmeas.ennreal_toReal
  have hB : ∀ j : ℕ, MeasurableSet (g ⁻¹' {j}) := fun j => hg (measurableSet_singleton j)
  let ηs : ℕ → Kernel α β := fun j => Kernel.piecewise (hB j) η 0
  have hfin : ∀ j, IsFiniteKernel (ηs j) := by
    intro j
    refine ⟨⟨(j : ℝ≥0∞) + 1, by simp [ENNReal.add_lt_top], fun a => ?_⟩⟩
    by_cases ha : a ∈ g ⁻¹' {j}
    · have hj : g a = j := ha
      have h1 : (η a Set.univ).toReal < (j : ℝ) + 1 := by
        have := Nat.lt_floor_add_one (η a Set.univ).toReal
        simpa [g, hj] using this
      have h2 : η a Set.univ = ENNReal.ofReal (η a Set.univ).toReal :=
        (ENNReal.ofReal_toReal (h a).ne).symm
      simp only [ηs, Kernel.piecewise_apply, if_pos ha]
      rw [h2]
      refine ENNReal.ofReal_le_of_le_toReal ?_
      rw [ENNReal.toReal_add (by simp) (by simp)]
      simpa using h1.le
    · have ha' : ¬ g a = j := ha
      simp [ηs, Kernel.piecewise_apply, ha']
  have hsum : η = Kernel.sum ηs := by
    ext a s hs
    rw [Kernel.sum_apply, Measure.sum_apply _ hs, tsum_eq_single (g a)]
    · simp [ηs, Kernel.piecewise_apply]
    · intro j hj
      have ha' : ¬ g a = j := fun h' => hj h'.symm
      simp [ηs, Kernel.piecewise_apply, ha']
  rw [hsum]
  exact ⟨⟨fun j => ηs j, hfin, rfl⟩⟩

/- English proof (translation)
Set `C : ℕ → Set β` to `disjointed (compactCovering β)`. Establish `hCm : ∀ k, MeasurableSet (C k)` using `fun k => MeasurableSet.disjointed (fun i => (isCompact_compactCovering β i).measurableSet) k`. Establish `hCd : Pairwise (Function.onFun Disjoint C)` using `disjoint_disjointed _`. Establish `hCu : ⋃ k, C k = Set.univ`. Simplify using `only [C, iUnion_disjointed]`.

Conclude with `iUnion_compactCovering β`. Establish `hCf : ∀ a k, κ a (C k) < ⊤` using `fun a k => by haveI := h a`. Conclude with `(measure_mono (disjointed_subset _ k)).trans_lt (isCompact_compactCovering β k).measure_lt_top`. Establish `hk : ∀ k, IsSFiniteKernel (Kernel.restrict κ (hCm k))` using `fun k => isSFiniteKernel_of_forall_univ_lt_top _ (fun a => by`. Rewrite using `[Kernel.restrict_apply]`.

Simplify using `using hCf a k)`. Establish `hsum : κ = Kernel.sum fun k => Kernel.restrict κ (hCm k)`. Use extensionality with `a s hs`. Rewrite using `[Kernel.sum_apply]`. Simplify using `only [Kernel.restrict_apply]`.

Rewrite using `[← Measure.restrict_iUnion hCd hCm, hCu, Measure.restrict_univ]`. Rewrite using `[hsum]`. Use `infer_instance`.
-/
theorem isSFiniteKernel_of_locallyFinite {α β : Type} [MeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] [T2Space β] [SigmaCompactSpace β]
    (κ : Kernel α β) (h : ∀ a, IsLocallyFiniteMeasure (κ a)) : IsSFiniteKernel κ := by
  let C : ℕ → Set β := disjointed (compactCovering β)
  have hCm : ∀ k, MeasurableSet (C k) := fun k =>
    MeasurableSet.disjointed (fun i => (isCompact_compactCovering β i).measurableSet) k
  have hCd : Pairwise (Function.onFun Disjoint C) := disjoint_disjointed _
  have hCu : ⋃ k, C k = Set.univ := by
    simp only [C, iUnion_disjointed]
    exact iUnion_compactCovering β
  have hCf : ∀ a k, κ a (C k) < ⊤ := fun a k => by
    haveI := h a
    exact (measure_mono (disjointed_subset _ k)).trans_lt
      (isCompact_compactCovering β k).measure_lt_top
  have hk : ∀ k, IsSFiniteKernel (Kernel.restrict κ (hCm k)) := fun k =>
    isSFiniteKernel_of_forall_univ_lt_top _ (fun a => by
      rw [Kernel.restrict_apply]
      simpa using hCf a k)
  have hsum : κ = Kernel.sum fun k => Kernel.restrict κ (hCm k) := by
    ext a s hs
    rw [Kernel.sum_apply]
    simp only [Kernel.restrict_apply]
    rw [← Measure.restrict_iUnion hCd hCm, hCu, Measure.restrict_univ]
  rw [hsum]
  infer_instance

/- English proof (translation)
Use `measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i => ?_` and prove the remaining obligations. Proceed by induction on `a using Fin.cases with`. Consider the case `zero`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero => simpa [vec] using measurable_fst`.

Consider the case `succ i => simpa [vec] using measurable_const`. Consider the case `succ j`. Proceed by induction on `i using Fin.cases with`. Consider the case `zero`. Simplify using `only [vec, Fin.cons_succ, Fin.cons_zero]`.

Conclude with `(measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)`. Consider the case `succ i`. Simplify using `only [vec, Fin.cons_succ]`. Conclude with `(measurable_pi_apply i).comp ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))`.
-/
theorem measurable_vec_triple {K : Type} [Zero K] [MeasurableSpace K] {M n : ℕ} :
    Measurable (fun p : K × (Fin n → K) × (Fin n → Fin M → K) =>
      (vec p.1 p.2.1 p.2.2 : Fin (n + 1) → Fin (M + 1) → K)) := by
  refine measurable_pi_lambda _ fun a => measurable_pi_lambda _ fun i => ?_
  induction a using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simpa [vec] using measurable_fst
    | succ i => simpa [vec] using measurable_const
  | succ j =>
    induction i using Fin.cases with
    | zero =>
      simp only [vec, Fin.cons_succ, Fin.cons_zero]
      exact (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
    | succ i =>
      simp only [vec, Fin.cons_succ]
      exact (measurable_pi_apply i).comp
        ((measurable_pi_apply j).comp (measurable_snd.comp measurable_snd))

/- English proof (translation)
Take `⟨iTR, iLR, iSR, iTR2, -⟩` from `D.hR`. Use `haveI := iTR`. Use `haveI := iLR`. Use `haveI := iSR`. Use `haveI := iTR2`.

Take `⟨iTK, iLK, iSK, iT2K, -, -, -, iBor, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R`. Use `haveI := iTK`. Use `haveI := iLK`. Use `haveI := iSK`. Use `haveI := iT2K`.

Establish `hJ'` using `GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht`. Take `⟨-, hloc, -, hmeas, -, -⟩` from `GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'`. Take `⟨-, hloc₁, -⟩` from `GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁`. Take `⟨-, -, iSH, -, iBH, hH⟩` from `GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R`. Use `haveI := iSH`.

Use `haveI := iBH`. Use `haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := iBor n M`. Use `haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := iBor (n + 1) (M + 1)`. Use `haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := iBor 1 (M + 1)`. Use `haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩`.

Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Establish `hact` using `(hH (n + 1)).1`. Establish `hten : Measurable (fun r : R => r ⊗ₜ[F] (1 : E))` using `by haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)`. Establish `hc : Continuous (fun r : R => r • (1 : R ⊗[F] E))` using `Continuous.smul (f := fun r : R => r) (g := fun _ : R => (1 : R ⊗[F] E)) continuous_id continuous_const`. Establish `he : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E)`.

Use function extensionality and compare the values at `r`. Simplify using `[Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']`. Rewrite using `[he]`. Conclude with `hc.measurable`. Set `κ : Kernel (HermR R σ n) (Fin n → Fin M → R ⊗[F] E)` to `⟨m', Measure.measurable_of_measurable_coe _ hmeas⟩`.

Use `haveI : IsSFiniteKernel κ := isSFiniteKernel_of_locallyFinite κ hloc`. Set `κ' : Kernel ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (Fin n → Fin M → R ⊗[F] E)` to `κ.comap (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))`. Use `haveI := hloc₁ (hermScal R σ (algebraMap F R t))`. Establish `hvec : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) => (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2 : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E))` using `measurable_vec_triple.comp ((hten.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk (((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk measurable_snd))`. Establish `hΦ : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) => actW R σ (blockOne (algebraMap F E t) J) (s q.1.2) (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2))` using `hact.measurable.comp ((D.hs.comp (measurable_snd.comp measurable_fst)).prodMk hvec)`.

Establish `hinner` using `Measurable.lintegral_kernel_prod_right' (κ := κ') (hφ.comp hΦ)`. Conclude with `Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner`.
-/
theorem measurable_Pint (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R]
    [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ)
    (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)
    (D : StageData σ J t n b lam m₁ m' s B₀ a κ₁ cm)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) (hφ : Measurable φ) :
    Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n =>
      Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  obtain ⟨iTR, iLR, iSR, iTR2, -⟩ := D.hR
  haveI := iTR
  haveI := iLR
  haveI := iSR
  haveI := iTR2
  obtain ⟨iTK, iLK, iSK, iT2K, -, -, -, iBor, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := iTK
  haveI := iLK
  haveI := iSK
  haveI := iT2K
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J D.hJ t D.ht
  obtain ⟨-, hloc, -, hmeas, -, -⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM M n J D.hJ R D.hR d b lam D.hlam m' D.hm'
  obtain ⟨-, hloc₁, -⟩ :=
    GlobalTheory.T.gram_fiber_measure_locally_finite_measurable_supported F E σ D.hCM (M + 1) 1 _ hJ' R D.hR d b lam D.hlam m₁ D.hm₁
  obtain ⟨-, -, iSH, -, iBH, hH⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ D.hCM (M + 1) _ hJ' R
  haveI := iSH
  haveI := iBH
  haveI : BorelSpace (Fin n → Fin M → R ⊗[F] E) := iBor n M
  haveI : BorelSpace (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) := iBor (n + 1) (M + 1)
  haveI : BorelSpace (Fin 1 → Fin (M + 1) → R ⊗[F] E) := iBor 1 (M + 1)
  haveI : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  have hact := (hH (n + 1)).1
  have hten : Measurable (fun r : R => r ⊗ₜ[F] (1 : E)) := by
    haveI : ContinuousSMul R (R ⊗[F] E) := IsModuleTopology.toContinuousSMul R (R ⊗[F] E)
    have hc : Continuous (fun r : R => r • (1 : R ⊗[F] E)) :=
      Continuous.smul (f := fun r : R => r) (g := fun _ : R => (1 : R ⊗[F] E))
        continuous_id continuous_const
    have he : (fun r : R => r ⊗ₜ[F] (1 : E)) = fun r : R => r • (1 : R ⊗[F] E) := by
      funext r
      simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul']
    rw [he]
    exact hc.measurable
  let κ : Kernel (HermR R σ n) (Fin n → Fin M → R ⊗[F] E) :=
    ⟨m', Measure.measurable_of_measurable_coe _ hmeas⟩
  haveI : IsSFiniteKernel κ := isSFiniteKernel_of_locallyFinite κ hloc
  let κ' : Kernel ((R × (Fin n → R ⊗[F] E) × HermR R σ n) × (Fin 1 → Fin (M + 1) → R ⊗[F] E))
      (Fin n → Fin M → R ⊗[F] E) :=
    κ.comap (fun p => p.1.2.2) (measurable_snd.comp (measurable_snd.comp measurable_fst))
  haveI := hloc₁ (hermScal R σ (algebraMap F R t))
  have hvec : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2 : Fin (n + 1) → Fin (M + 1) → R ⊗[F] E)) :=
    measurable_vec_triple.comp ((hten.comp (measurable_fst.comp (measurable_fst.comp measurable_fst))).prodMk
      (((measurable_fst.comp (measurable_snd.comp (measurable_fst.comp measurable_fst)))).prodMk
        measurable_snd))
  have hΦ : Measurable (fun q : ((R × (Fin n → R ⊗[F] E) × HermR R σ n) ×
      (Fin 1 → Fin (M + 1) → R ⊗[F] E)) × (Fin n → Fin M → R ⊗[F] E) =>
        actW R σ (blockOne (algebraMap F E t) J) (s q.1.2)
          (vec (q.1.1.1 ⊗ₜ[F] (1 : E)) q.1.1.2.1 q.2)) :=
    hact.measurable.comp ((D.hs.comp (measurable_snd.comp measurable_fst)).prodMk hvec)
  have hinner := Measurable.lintegral_kernel_prod_right' (κ := κ') (hφ.comp hΦ)
  exact Measurable.lintegral_prod_right' (ν := m₁ (hermScal R σ (algebraMap F R t))) hinner

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
