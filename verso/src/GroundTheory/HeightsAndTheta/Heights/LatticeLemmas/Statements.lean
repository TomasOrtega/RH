import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsExamples
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt IsDedekindDomain
open GroundTheory.Heights₂.Heights

universe u v w

noncomputable section

def BaseChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (L : Type w) [Field L] [NumberField L] [Algebra K L]
    (M : HermitianBundle.{v} K), (M.baseChange L).deg = M.deg

def Sublattice.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier),
    Module.finrank (𝓞 K) F = Module.finrank (𝓞 K) M.carrier →
      M.deg = (M.sub F).deg + Real.log (Nat.card (M.carrier ⧸ F)) / Module.finrank ℚ K ∧
        (M.sub F).deg ≤ M.deg

def LatticeOfLocalisations.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (V : Type v) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M₁ : FullLattice K V)
    (N N'' : ∀ v : HeightOneSpectrum (𝓞 K),
      Submodule (v.adicCompletionIntegers K) (v.adicCompletion K ⊗[K] V)),
    (∀ v, IsLocalLattice v (N v)) → {v | N v ≠ localLattice v M₁.carrier}.Finite →
    (∀ v, IsLocalLattice v (N'' v)) → {v | N'' v ≠ localLattice v M₁.carrier}.Finite →
      (latticeOfLocal N).FG ∧ Submodule.span K (latticeOfLocal N : Set V) = ⊤ ∧
        (∀ v, localLattice v (latticeOfLocal N) = N v) ∧
        (latticeOfLocal N ≤ latticeOfLocal N'' ↔ ∀ v, N v ≤ N'' v)

def LocalChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (V : Type v) [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Nm : HermitianNorms K V) (M₁ M₂ : FullLattice K V)
    (g : ∀ v : HeightOneSpectrum (𝓞 K),
      (v.adicCompletion K ⊗[K] V) ≃ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)),
    {v | g v ≠ 1}.Finite →
    (∀ v, (localLattice v M₂.carrier : Set (v.adicCompletion K ⊗[K] V)) =
      g v '' localLattice v M₁.carrier) →
      (Nm.bundle M₂).deg = (Nm.bundle M₁).deg +
        (∑ᶠ v, Real.log ‖LinearMap.det
          ((g v : (v.adicCompletion K ⊗[K] V) →ₗ[v.adicCompletion K] (v.adicCompletion K ⊗[K] V)))‖) /
          Module.finrank ℚ K

def NormComparison.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (h' : HermitianMetric K M.carrier) (A : (K →+* ℂ) → ℝ),
    (∀ (σ : K →+* ℂ) (x : Fibre σ M.carrier),
      ‖FibreSpace.equiv h' σ x‖ ≤ A σ * ‖FibreSpace.equiv M.metric σ x‖) →
      M.deg - Module.finrank (𝓞 K) M.carrier * (∑ σ : K →+* ℂ, Real.log (A σ)) /
          Module.finrank ℚ K ≤ (⟨M.carrier, h'⟩ : HermitianBundle.{v} K).deg

def DiagonalChange.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (h' : HermitianMetric K M.carrier)
    (T : ∀ σ : K →+* ℂ, Fibre σ M.carrier →ₗ[ℂ] Fibre σ M.carrier),
    (∀ (σ : K →+* ℂ) (x : Fibre σ M.carrier),
      ‖FibreSpace.equiv h' σ x‖ = ‖FibreSpace.equiv M.metric σ (T σ x)‖) →
    (∀ σ : K →+* ℂ, ∃ (n : ℕ) (b : OrthonormalBasis (Fin n) ℂ (FibreSpace M.metric σ))
      (d : Fin n → ℂ), ∀ i, FibreSpace.equiv M.metric σ
        (T σ ((FibreSpace.equiv M.metric σ).symm (b i))) = d i • b i) →
      (⟨M.carrier, h'⟩ : HermitianBundle.{v} K).deg =
        M.deg - (∑ σ : K →+* ℂ, Real.log ‖LinearMap.det (T σ)‖) / Module.finrank ℚ K

def ExactSequence.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F),
    M.deg = (M.sub F).deg + (M.quot F hF).deg

def ChainSum.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K) (k : ℕ)
    (c : Fin (k + 1) → Submodule (𝓞 K) M.carrier),
    c 0 = ⊤ → Antitone c → ∀ hc : ∀ a, M.Saturated (c a),
      M.deg = (M.sub (c (Fin.last k))).deg +
        ∑ a : Fin k, ((M.sub (c a.castSucc)).quot ((c a.succ).comap (c a.castSucc).subtype)
          ((hc a.succ).comap_subtype _)).deg

def Hadamard.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K) {ι : Type w} [Fintype ι]
    (x : ι → M.carrier) (La : ℝ),
    LinearIndependent (𝓞 K) x → Fintype.card ι = Module.finrank (𝓞 K) M.carrier →
    (∀ i (σ : K →+* ℂ), M.normAt σ (x i) ≤ La) →
      -(Module.finrank (𝓞 K) M.carrier * Real.log La) ≤ M.deg

def HadamardQuotient.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F) {ι : Type w} (x : ι → M.carrier) (La : ℝ),
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range x)) = Module.finrank (𝓞 K) M.carrier →
    (∀ i (σ : K →+* ℂ), M.normAt σ (x i) ≤ La) →
      -(Module.finrank (𝓞 K) (M.carrier ⧸ F) * Real.log La) ≤ (M.quot F hF).deg

def HadamardMean.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K) {ι : Type w} [Fintype ι]
    (x : ι → M.carrier),
    LinearIndependent (𝓞 K) x → Fintype.card ι = Module.finrank (𝓞 K) M.carrier →
      -(∑ i, ∑ σ : K →+* ℂ, Real.log (M.normAt σ (x i))) / Module.finrank ℚ K ≤ M.deg

def HadamardMeanQuotient.Statement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (M : HermitianBundle.{v} K)
    (F : Submodule (𝓞 K) M.carrier) (hF : M.Saturated F) {ι : Type w} (x : ι → M.carrier),
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range x)) = Module.finrank (𝓞 K) M.carrier →
      ∃ s : Fin (Module.finrank (𝓞 K) (M.carrier ⧸ F)) → ι,
        LinearIndependent (𝓞 K) (fun j ↦ F.mkQ (x (s j))) ∧
        -(∑ j, ∑ σ : K →+* ℂ, Real.log (M.normAt σ (x (s j)))) / Module.finrank ℚ K ≤
          (M.quot F hF).deg

section Witnesses

variable (K : Type u) [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `(HermitianBundle.standard K 2).sub (standardFlag K 1)`.
-/
example : HermitianBundle K := (HermitianBundle.standard K 2).sub (standardFlag K 1)
/- English proof (translation)
The claim follows from `(HermitianBundle.standard K 2).quot (standardFlag K 1) (standardFlag_saturated 1)`.
-/
example : HermitianBundle K :=
  (HermitianBundle.standard K 2).quot (standardFlag K 1) (standardFlag_saturated 1)
/- English proof (translation)
The claim follows from `(HermitianBundle.standard ℚ 2).quot (standardFlag ℚ 1) (standardFlag_saturated 1)`.
-/
example : HermitianBundle ℚ := (HermitianBundle.standard ℚ 2).quot (standardFlag ℚ 1)
  (standardFlag_saturated 1)
/- English proof (translation)
The claim follows from `(HermitianBundle.standard GaussianField 2).quot (standardFlag GaussianField 1) (standardFlag_saturated 1)`.
-/
example : HermitianBundle GaussianField := (HermitianBundle.standard GaussianField 2).quot
  (standardFlag GaussianField 1) (standardFlag_saturated 1)
/- English proof (translation)
The claim follows from `(HermitianBundle.standard ℚ 2).baseChange GaussianField`.
-/
example : HermitianBundle GaussianField := (HermitianBundle.standard ℚ 2).baseChange GaussianField
/- English proof (translation)
The claim follows from `(HermitianNorms.standard GaussianField 2).bundle (FullLattice.standard GaussianField 2)`.
-/
example : HermitianBundle GaussianField :=
  (HermitianNorms.standard GaussianField 2).bundle (FullLattice.standard GaussianField 2)

def doubled : Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  LinearMap.range ((2 : 𝓞 K) • LinearMap.id)

/- English proof (translation)
The claim follows from `LinearMap.finrank_range_of_inj (by intro x y hxy simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy exact smul_right_injective (Fin 2 → 𝓞 K) (two_ne_zero (α := 𝓞 K)) hxy)`.
-/
theorem Sublattice.witness :
    Module.finrank (𝓞 K) (doubled K) =
      Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  LinearMap.finrank_range_of_inj (by
    intro x y hxy
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
    exact smul_right_injective (Fin 2 → 𝓞 K) (two_ne_zero (α := 𝓞 K)) hxy)

/- English proof (translation)
The claim follows from `Sublattice.witness ℚ`.
-/
example := Sublattice.witness ℚ
/- English proof (translation)
The claim follows from `Sublattice.witness GaussianField`.
-/
example := Sublattice.witness GaussianField

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun v ↦ localLattice_isLocalLattice v _, Set.finite_empty.subset fun _ hv ↦ hv rfl⟩`.
-/
theorem LatticeOfLocalisations.witness :
    (∀ v, IsLocalLattice v (localLattice v (FullLattice.standard K 2).carrier)) ∧
      {v : HeightOneSpectrum (𝓞 K) | localLattice v (FullLattice.standard K 2).carrier ≠
        localLattice v (FullLattice.standard K 2).carrier}.Finite :=
  ⟨fun v ↦ localLattice_isLocalLattice v _, Set.finite_empty.subset fun _ hv ↦ hv rfl⟩

/- English proof (translation)
The claim follows from `LatticeOfLocalisations.witness ℚ`.
-/
example := LatticeOfLocalisations.witness ℚ
/- English proof (translation)
The claim follows from `LatticeOfLocalisations.witness GaussianField`.
-/
example := LatticeOfLocalisations.witness GaussianField

/- English proof (translation)
Assemble the required witnesses or components as `⟨swapAt_finite v₀, localLattice_swapAt v₀⟩`.
-/
theorem LocalChange.witness (v₀ : HeightOneSpectrum (𝓞 K)) :
    {v | swapAt v₀ v ≠ 1}.Finite ∧
      ∀ v, (localLattice v (FullLattice.standard K 2).carrier : Set _) =
        swapAt v₀ v '' localLattice v (FullLattice.standard K 2).carrier :=
  ⟨swapAt_finite v₀, localLattice_swapAt v₀⟩

/- English proof (translation)
The claim follows from `LocalChange.witness ℚ (nonempty_heightOneSpectrum (K := ℚ)).some`.
-/
example := LocalChange.witness ℚ (nonempty_heightOneSpectrum (K := ℚ)).some
/- English proof (translation)
The claim follows from `LocalChange.witness GaussianField (nonempty_heightOneSpectrum (K := GaussianField)).some`.
-/
example := LocalChange.witness GaussianField (nonempty_heightOneSpectrum (K := GaussianField)).some

variable {K} in

/- English proof (translation)
Establish `h1` using `norm_sq_eq_re_inner (𝕜 := ℂ) (FibreSpace.equiv (h.scale c hc) σ x)`. Establish `h2` using `norm_sq_eq_re_inner (𝕜 := ℂ) (FibreSpace.equiv h σ x)`. Establish `h3 : ‖FibreSpace.equiv (h.scale c hc) σ x‖ ^ 2 = (c * ‖FibreSpace.equiv h σ x‖) ^ 2`. Rewrite using `[h1, mul_pow, h2]`. Conclude with `Complex.re_ofReal_mul _ _`.

Rewrite using `[← Real.sqrt_sq (norm_nonneg (FibreSpace.equiv (h.scale c hc) σ x)), h3, Real.sqrt_sq (by positivity)]`.
-/
theorem norm_scale {E : Type*} [AddCommGroup E] [Module (𝓞 K) E] [Module.Finite (𝓞 K) E]
    [Module.Projective (𝓞 K) E] (h : HermitianMetric K E) (c : ℝ) (hc : 0 < c) (σ : K →+* ℂ)
    (x : Fibre σ E) :
    ‖FibreSpace.equiv (h.scale c hc) σ x‖ = c * ‖FibreSpace.equiv h σ x‖ := by
  have h1 := norm_sq_eq_re_inner (𝕜 := ℂ) (FibreSpace.equiv (h.scale c hc) σ x)
  have h2 := norm_sq_eq_re_inner (𝕜 := ℂ) (FibreSpace.equiv h σ x)
  have h3 : ‖FibreSpace.equiv (h.scale c hc) σ x‖ ^ 2 = (c * ‖FibreSpace.equiv h σ x‖) ^ 2 := by
    rw [h1, mul_pow, h2]
    exact Complex.re_ofReal_mul _ _
  rw [← Real.sqrt_sq (norm_nonneg (FibreSpace.equiv (h.scale c hc) σ x)), h3,
    Real.sqrt_sq (by positivity)]

/- English proof (translation)
The claim follows from `(norm_scale _ 2 two_pos σ x).le`.
-/
theorem NormComparison.witness (σ : K →+* ℂ) (x : Fibre σ (HermitianBundle.standard K 2).carrier) :
    ‖FibreSpace.equiv ((HermitianBundle.standard K 2).metric.scale 2 two_pos) σ x‖ ≤
      2 * ‖FibreSpace.equiv (HermitianBundle.standard K 2).metric σ x‖ :=
  (norm_scale _ 2 two_pos σ x).le

/- English proof (translation)
The claim follows from `NormComparison.witness ℚ`.
-/
example := NormComparison.witness ℚ
/- English proof (translation)
The claim follows from `NormComparison.witness GaussianField`.
-/
example := NormComparison.witness GaussianField

/- English proof (translation)
Use `⟨fun σ x ↦ ?_, fun σ ↦ ⟨_, stdOrthonormalBasis ℂ _, fun _ ↦ 2, fun i ↦ ?_⟩⟩` and prove the remaining obligations. Rewrite using `[norm_scale, LinearMap.smul_apply, LinearMap.id_apply, map_smul, norm_smul, Complex.norm_two]`. Rewrite using `[LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearEquiv.apply_symm_apply]`.
-/
theorem DiagonalChange.witness :
    (∀ (σ : K →+* ℂ) (x : Fibre σ (HermitianBundle.standard K 2).carrier),
      ‖FibreSpace.equiv ((HermitianBundle.standard K 2).metric.scale 2 two_pos) σ x‖ =
        ‖FibreSpace.equiv (HermitianBundle.standard K 2).metric σ
          (((2 : ℂ) • LinearMap.id : Fibre σ (HermitianBundle.standard K 2).carrier →ₗ[ℂ] _) x)‖) ∧
    ∀ σ : K →+* ℂ, ∃ (n : ℕ)
      (b : OrthonormalBasis (Fin n) ℂ (FibreSpace (HermitianBundle.standard K 2).metric σ))
      (d : Fin n → ℂ), ∀ i, FibreSpace.equiv (HermitianBundle.standard K 2).metric σ
        (((2 : ℂ) • LinearMap.id : Fibre σ (HermitianBundle.standard K 2).carrier →ₗ[ℂ] _)
          ((FibreSpace.equiv (HermitianBundle.standard K 2).metric σ).symm (b i))) = d i • b i := by
  refine ⟨fun σ x ↦ ?_, fun σ ↦ ⟨_, stdOrthonormalBasis ℂ _, fun _ ↦ 2, fun i ↦ ?_⟩⟩
  · rw [norm_scale, LinearMap.smul_apply, LinearMap.id_apply, map_smul, norm_smul,
      Complex.norm_two]
  · rw [LinearMap.smul_apply, LinearMap.id_apply, map_smul, LinearEquiv.apply_symm_apply]

/- English proof (translation)
The claim follows from `DiagonalChange.witness ℚ`.
-/
example := DiagonalChange.witness ℚ
/- English proof (translation)
The claim follows from `DiagonalChange.witness GaussianField`.
-/
example := DiagonalChange.witness GaussianField

/- English proof (translation)
The claim follows from `standardFlag_saturated 1`.
-/
theorem ExactSequence.witness : (HermitianBundle.standard K 2).Saturated (standardFlag K 1) :=
  standardFlag_saturated 1

/- English proof (translation)
The claim follows from `ExactSequence.witness ℚ`.
-/
example := ExactSequence.witness ℚ
/- English proof (translation)
The claim follows from `ExactSequence.witness GaussianField`.
-/
example := ExactSequence.witness GaussianField

def flagChain : Fin 3 → Submodule (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  fun i ↦ standardFlag K i.rev

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl, fun _ _ hij ↦ standardFlag_monotone (Fin.rev_le_rev.mpr hij), fun _ ↦ standardFlag_saturated _⟩`.
-/
theorem ChainSum.witness :
    flagChain K 0 = ⊤ ∧ Antitone (flagChain K) ∧
      ∀ a, (HermitianBundle.standard K 2).Saturated (flagChain K a) :=
  ⟨rfl, fun _ _ hij ↦ standardFlag_monotone (Fin.rev_le_rev.mpr hij),
    fun _ ↦ standardFlag_saturated _⟩

/- English proof (translation)
The claim follows from `ChainSum.witness ℚ`.
-/
example := ChainSum.witness ℚ
/- English proof (translation)
The claim follows from `ChainSum.witness GaussianField`.
-/
example := ChainSum.witness GaussianField

def stdVec : Fin 2 → (HermitianBundle.standard K 2).carrier := fun i ↦ Pi.single i 1

/- English proof (translation)
The claim follows from `funext fun i ↦ (Pi.basisFun_apply (𝓞 K) (Fin 2) i).symm`.
-/
theorem stdVec_eq : stdVec K = ⇑(Pi.basisFun (𝓞 K) (Fin 2)) :=
  funext fun i ↦ (Pi.basisFun_apply (𝓞 K) (Fin 2) i).symm

/- English proof (translation)
Rewrite using `[stdVec_eq]`. Conclude with `(Pi.basisFun (𝓞 K) (Fin 2)).linearIndependent`.
-/
theorem stdVec_linearIndependent : LinearIndependent (𝓞 K) (stdVec K) := by
  rw [stdVec_eq]
  exact (Pi.basisFun (𝓞 K) (Fin 2)).linearIndependent

/- English proof (translation)
Rewrite using `[Fintype.card_fin]`. Conclude with `(Module.finrank_fin_fun (𝓞 K)).symm`.
-/
theorem stdVec_card :
    Fintype.card (Fin 2) = Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier := by
  rw [Fintype.card_fin]
  exact (Module.finrank_fin_fun (𝓞 K)).symm

/- English proof (translation)
Rewrite using `[finrank_span_eq_card (stdVec_linearIndependent K)]`. Conclude with `stdVec_card K`.
-/
theorem stdVec_span :
    Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range (stdVec K))) =
      Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier := by
  rw [finrank_span_eq_card (stdVec_linearIndependent K)]
  exact stdVec_card K

/- English proof (translation)
Establish `h` using `norm_fibreVec_sq (HermitianMetric.standard K (Fin 2)) σ (Pi.single i 1)`. Rewrite `h` using `[HermitianMetric.standard_inner_single, Complex.one_re]`. Rewrite using `[HermitianBundle.normAt, ← Real.sqrt_sq (norm_nonneg _)]`. Conclude with `(congrArg Real.sqrt h).trans Real.sqrt_one`.
-/
theorem normAt_stdVec (σ : K →+* ℂ) (i : Fin 2) :
    (HermitianBundle.standard K 2).normAt σ (stdVec K i) = 1 := by
  have h := norm_fibreVec_sq (HermitianMetric.standard K (Fin 2)) σ (Pi.single i 1)
  rw [HermitianMetric.standard_inner_single, Complex.one_re] at h
  rw [HermitianBundle.normAt, ← Real.sqrt_sq (norm_nonneg _)]
  exact (congrArg Real.sqrt h).trans Real.sqrt_one

/- English proof (translation)
Assemble the required witnesses or components as `⟨stdVec_linearIndependent K, stdVec_card K, fun i σ ↦ (normAt_stdVec K σ i).le⟩`.
-/
theorem Hadamard.witness :
    LinearIndependent (𝓞 K) (stdVec K) ∧
      Fintype.card (Fin 2) = Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier ∧
        ∀ i (σ : K →+* ℂ), (HermitianBundle.standard K 2).normAt σ (stdVec K i) ≤ 1 :=
  ⟨stdVec_linearIndependent K, stdVec_card K, fun i σ ↦ (normAt_stdVec K σ i).le⟩

/- English proof (translation)
The claim follows from `Hadamard.witness ℚ`.
-/
example := Hadamard.witness ℚ
/- English proof (translation)
The claim follows from `Hadamard.witness GaussianField`.
-/
example := Hadamard.witness GaussianField

/- English proof (translation)
Assemble the required witnesses or components as `⟨standardFlag_saturated 1, stdVec_span K, fun i σ ↦ (normAt_stdVec K σ i).le⟩`.
-/
theorem HadamardQuotient.witness :
    (HermitianBundle.standard K 2).Saturated (standardFlag K 1) ∧
      Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range (stdVec K))) =
        Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier ∧
        ∀ i (σ : K →+* ℂ), (HermitianBundle.standard K 2).normAt σ (stdVec K i) ≤ 1 :=
  ⟨standardFlag_saturated 1, stdVec_span K, fun i σ ↦ (normAt_stdVec K σ i).le⟩

/- English proof (translation)
The claim follows from `HadamardQuotient.witness ℚ`.
-/
example := HadamardQuotient.witness ℚ
/- English proof (translation)
The claim follows from `HadamardQuotient.witness GaussianField`.
-/
example := HadamardQuotient.witness GaussianField

/- English proof (translation)
Assemble the required witnesses or components as `⟨stdVec_linearIndependent K, stdVec_card K⟩`.
-/
theorem HadamardMean.witness :
    LinearIndependent (𝓞 K) (stdVec K) ∧
      Fintype.card (Fin 2) = Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  ⟨stdVec_linearIndependent K, stdVec_card K⟩

/- English proof (translation)
The claim follows from `HadamardMean.witness ℚ`.
-/
example := HadamardMean.witness ℚ
/- English proof (translation)
The claim follows from `HadamardMean.witness GaussianField`.
-/
example := HadamardMean.witness GaussianField

/- English proof (translation)
Assemble the required witnesses or components as `⟨standardFlag_saturated 1, stdVec_span K⟩`.
-/
theorem HadamardMeanQuotient.witness :
    (HermitianBundle.standard K 2).Saturated (standardFlag K 1) ∧
      Module.finrank (𝓞 K) (Submodule.span (𝓞 K) (Set.range (stdVec K))) =
        Module.finrank (𝓞 K) (HermitianBundle.standard K 2).carrier :=
  ⟨standardFlag_saturated 1, stdVec_span K⟩

/- English proof (translation)
The claim follows from `HadamardMeanQuotient.witness ℚ`.
-/
example := HadamardMeanQuotient.witness ℚ
/- English proof (translation)
The claim follows from `HadamardMeanQuotient.witness GaussianField`.
-/
example := HadamardMeanQuotient.witness GaussianField

/- English proof (translation)
The claim follows from `inferInstance`.
-/
example : Algebra ℚ GaussianField := inferInstance

end Witnesses

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
