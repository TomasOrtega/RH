import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianMatricesLocallyCompactBorelStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitsOpenEmbeddingLocalTensorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRingStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF.ToOld

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `w hw`. Establish `hj : ∀ j, ∑ b, w b * X b j = 0` using `fun j => by`. Use `congrFun hw j` as an intermediate fact. Simplify `this` using `[Finset.sum_apply]`.

Establish `hmul : (gramR R σ J X).mulVec w = 0`. Use function extensionality and compare the values at `a`. Use `show ∑ b, hform (sigR R σ) (JR R J) (X a) (X b) * w b = 0`. Simplify using `only [hform, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Establish `: ∑ b, sigR R σ (X a i) * JR R J i j * X b j * w b = sigR R σ (X a i) * JR R J i j * ∑ b, w b * X b j`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun b _ => by ring`. Rewrite using `[this, hj j, mul_zero]`. Establish `h1` using `congrArg (Matrix.mulVec (gramR R σ J X)⁻¹) hmul`. Rewrite `h1` using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec, Matrix.mulVec_zero]`. Conclude with `fun i => congrFun h1 i`.
-/
theorem linearIndependent_of_isUnit_gram {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R]
    [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E)
    (h : IsUnit (gramR R σ J X).det) : LinearIndependent (R ⊗[F] E) X := by
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hj : ∀ j, ∑ b, w b * X b j = 0 := fun j => by
    have := congrFun hw j
    simpa [Finset.sum_apply] using this
  have hmul : (gramR R σ J X).mulVec w = 0 := by
    funext a
    show ∑ b, hform (sigR R σ) (JR R J) (X a) (X b) * w b = 0
    simp only [hform, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    have : ∑ b, sigR R σ (X a i) * JR R J i j * X b j * w b =
        sigR R σ (X a i) * JR R J i j * ∑ b, w b * X b j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [this, hj j, mul_zero]
  have h1 := congrArg (Matrix.mulVec (gramR R σ J X)⁻¹) hmul
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec, Matrix.mulVec_zero] at h1
  exact fun i => congrFun h1 i

open Classical in

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `h`. Use `⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hs ht => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hb : b ∈ B`. Simplify using `only [hb, if_true]`. Use `measure_mono_null (Set.compl_subset_compl.2 fun v hv => ⟨hv.1, ?_⟩) (h1 b)` and prove the remaining obligations.

Conclude with `(hUB v b hv.1).2 hb`. Simplify using `[hb]`. Establish `key` using `h2 (U.indicator φ) (hφ.indicator hU)`. Rewrite `key` using `[lintegral_indicator hU, Measure.restrict_restrict hU, Set.inter_eq_left.2 hUW]`. Rewrite using `[key]`.

Use `lintegral_congr fun b => ?_` and prove the remaining obligations. Establish `hae : ∀ᵐ v ∂(fib b), f v = ι b`. Establish `: ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ W` using `mem_ae_iff.2 (h1 b)`. Use `filter_upwards [this] with v hv using hv.1`. Distinguish the cases in `hb : b ∈ B`.

Simplify using `only [hb, if_true]`. Use `lintegral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [hae] with v hv`. Conclude with `Set.indicator_of_mem ((hUB v b hv).2 hb) φ`. Simplify using `only [hb, if_false, lintegral_zero_measure]`.

Use `(lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero` and prove the remaining obligations. Use `filter_upwards [hae] with v hv`. Conclude with `Set.indicator_of_notMem (fun hvU => hb ((hUB v b hv).1 hvU)) φ`. Take `⟨k1, k2⟩` from `h3 φ hc hs (ht.trans hUW)`. Use `⟨fun b hb => ?_, ?_⟩` and prove the remaining obligations.

Simplify `k1 b (Set.mem_univ b)` using `only [hb, if_true]`. Conclude with `(k2.mono (Set.subset_univ B)).congr fun b hb => by simp only [hb, if_true]`.
-/
theorem isFibreFamily_restrict {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V] [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure V) (f : V → Y) (ι : X → Y) (U W : Set V) (ν : Measure X)
    (B : Set X) (fib : X → Measure V) (hUW : U ⊆ W) (hU : MeasurableSet U)
    (hUB : ∀ v b, f v = ι b → (v ∈ U ↔ b ∈ B))
    (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι W ν Set.univ fib) :
    Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν B (fun b => if b ∈ B then fib b else 0) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun b => ?_, fun φ hφ => ?_, fun φ hc hs ht => ?_⟩
  · by_cases hb : b ∈ B
    · simp only [hb, if_true]
      refine measure_mono_null (Set.compl_subset_compl.2 fun v hv => ⟨hv.1, ?_⟩) (h1 b)
      exact (hUB v b hv.1).2 hb
    · simp [hb]
  · have key := h2 (U.indicator φ) (hφ.indicator hU)
    rw [lintegral_indicator hU, Measure.restrict_restrict hU, Set.inter_eq_left.2 hUW] at key
    rw [key]
    refine lintegral_congr fun b => ?_
    have hae : ∀ᵐ v ∂(fib b), f v = ι b := by
      have : ∀ᵐ v ∂(fib b), v ∈ f ⁻¹' {ι b} ∩ W := mem_ae_iff.2 (h1 b)
      filter_upwards [this] with v hv using hv.1
    by_cases hb : b ∈ B
    · simp only [hb, if_true]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with v hv
      exact Set.indicator_of_mem ((hUB v b hv).2 hb) φ
    · simp only [hb, if_false, lintegral_zero_measure]
      refine (lintegral_congr_ae (g := fun _ => 0) ?_).trans lintegral_zero
      filter_upwards [hae] with v hv
      exact Set.indicator_of_notMem (fun hvU => hb ((hUB v b hv).1 hvU)) φ
  · obtain ⟨k1, k2⟩ := h3 φ hc hs (ht.trans hUW)
    refine ⟨fun b hb => ?_, ?_⟩
    · simpa only [hb, if_true] using k1 b (Set.mem_univ b)
    · exact (k2.mono (Set.subset_univ B)).congr fun b hb => by simp only [hb, if_true]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D`. Take `⟨iTR, iLC, iSC, iT2, -⟩` from `id D.hR`. Use `haveI := iTR`. Use `haveI := iLC`. Use `haveI := iSC`.

Use `haveI := iT2`. Take `⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩` from `GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R`. Use `haveI := kTR`. Use `haveI := kLC`. Use `haveI := kSC`.

Use `haveI := kT2`. Use `haveI := kB n M`. Take `⟨-, -, -, -, hg⟩` from `GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n`. Take `⟨g, gc, hgg⟩` from `hg M J D.hJ`. Establish `hopen : IsOpen (Unt σ R n)`.

Establish `hu : IsOpen {x : R ⊗[F] E | IsUnit x}`. Use `(GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR).isOpen_range` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`. Simplify using `[IsUnit]`.

Establish `hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det` using `continuous_subtype_val.matrix_det`. Conclude with `hu.preimage hc`. Establish `hset : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' (Unt σ R n)`. Use extensionality with `X`. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage, Unt, hgg X]`.

Establish `hmeas : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det}`. Rewrite using `[hset]`. Conclude with `(hopen.preimage gc).measurableSet`. Establish `hfam` using `isFibreFamily_restrict (coordW R b lam n M) (gramR R σ J) Subtype.val {X | IsUnit (gramR R σ J X).det} {X | LinearIndependent (R ⊗[F] E) X} (coordHerm R σ b lam n) {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m' (fun X hX => linearIndependent_of_isUnit_gram R σ J X hX …`. Conclude with `⟨_, { hCM := D.hCM, hJ := D.hJ, ht := D.ht, hR := D.hR, hlam := D.hlam, hm₁ := D.hm₁, hm' := hfam, hs := D.hs, hsec := D.hsec, hcpt := D.hcpt, hB₀ := D.hB₀, htB := D.htB, hac := D.hac, hoff := D.hoff, hsq := D.hsq, ha1 := D.ha1, hκc := D.hκc, hκ1 := D.hκ1, hscale := D.hscale, hcm …`.
-/
theorem stageData_of_stageDataF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∃ m₀ : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E), StageData σ J t n b lam m₁ m₀ s B₀ a κ₁ cm := by
  intro F E _ _ _ _ _ σ M J t n R _ _ _ _ _ d b lam m₁ m' s B₀ a κ₁ cm D
  obtain ⟨iTR, iLC, iSC, iT2, -⟩ := id D.hR
  haveI := iTR; haveI := iLC; haveI := iSC; haveI := iT2
  obtain ⟨kTR, kLC, kSC, kT2, -, -, -, kB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ D.hCM R
  haveI := kTR; haveI := kLC; haveI := kSC; haveI := kT2
  haveI := kB n M
  obtain ⟨-, -, -, -, hg⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ D.hCM R n
  obtain ⟨g, gc, hgg⟩ := hg M J D.hJ
  have hopen : IsOpen (Unt σ R n) := by
    have hu : IsOpen {x : R ⊗[F] E | IsUnit x} := by
      have := (GlobalTheory.T.units_open_embedding_local_tensor F E σ D.hCM R D.hR).isOpen_range
      convert this using 1
      ext x
      simp [IsUnit]
    have hc : Continuous fun S : HermR R σ n => (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det :=
      continuous_subtype_val.matrix_det
    exact hu.preimage hc
  have hset : {X | IsUnit (gramR R σ J X).det} = g ⁻¹' (Unt σ R n) := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Unt, hgg X]
  have hmeas : MeasurableSet {X : Fin n → Fin M → R ⊗[F] E | IsUnit (gramR R σ J X).det} := by
    rw [hset]
    exact (hopen.preimage gc).measurableSet
  have hfam := isFibreFamily_restrict (coordW R b lam n M) (gramR R σ J) Subtype.val
    {X | IsUnit (gramR R σ J X).det} {X | LinearIndependent (R ⊗[F] E) X} (coordHerm R σ b lam n)
    {S | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} m'
    (fun X hX => linearIndependent_of_isUnit_gram R σ J X hX) hmeas
    (fun X S hX => by simp only [Set.mem_setOf_eq, hX]) D.hm'
  exact ⟨_, { hCM := D.hCM, hJ := D.hJ, ht := D.ht, hR := D.hR, hlam := D.hlam, hm₁ := D.hm₁, hm' := hfam,
              hs := D.hs, hsec := D.hsec, hcpt := D.hcpt, hB₀ := D.hB₀, htB := D.htB, hac := D.hac,
              hoff := D.hoff, hsq := D.hsq, ha1 := D.ha1, hκc := D.hκc, hκ1 := D.hκ1, hscale := D.hscale,
              hcmc := D.hcmc, hmod := D.hmod }⟩

end GlobalTheory.CompanionTheory.SW.StageF.ToOld
