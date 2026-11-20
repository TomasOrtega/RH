import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt MeasureTheory Module Filter
  Topology Asymptotics Matrix
open scoped ComplexOrder

noncomputable section

section Had

variable {K : Type*} [Field K] [NumberField K]

def fibreNorm (E : HermitianBundle K) (σ : K →+* ℂ) (x : Fibre σ E.carrier) : ℝ :=
  ‖FibreSpace.equiv E.metric σ x‖

def bundleDegree (E : HermitianBundle K) : ℝ := E.normDegree ⊤

abbrev bundleRank (E : HermitianBundle K) : ℕ := Module.finrank (𝓞 K) E.carrier

variable (K) in

def meanLog (f : (K →+* ℂ) → ℝ) : ℝ := (∑ σ : K →+* ℂ, Real.log (f σ)) / Module.finrank ℚ K

structure BoundedInjection (E' E : HermitianBundle K) (A : (K →+* ℂ) → ℝ) where

  toLinearMap : E'.carrier →ₗ[𝓞 K] E.carrier
  injective : Function.Injective toLinearMap
  norm_le : ∀ (σ : K →+* ℂ) (x : Fibre σ E'.carrier),
    fibreNorm E σ (toLinearMap.lTensor (ComplexAt σ) x) ≤ A σ * fibreNorm E' σ x

structure ShortFamily (E : HermitianBundle K) (lam : (K →+* ℂ) → ℝ) where

  vec : Fin (bundleRank E) → E.carrier
  linearIndependent : LinearIndependent (𝓞 K) vec
  norm_le : ∀ (σ : K →+* ℂ) (i : Fin (bundleRank E)),
    fibreNorm E σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] vec i) ≤ lam σ

end Had

def Had.Statement : Prop :=
  (∀ (K : Type) [Field K] [NumberField K] (E' E : HermitianBundle.{0} K)
      (A lam : (K →+* ℂ) → ℝ), BoundedInjection E' E A → ShortFamily E lam →
      bundleDegree E' ≤ bundleDegree E + bundleRank E' * meanLog K A +
        ((bundleRank E : ℝ) - bundleRank E') * meanLog K lam) ∧
  (∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (lam : (K →+* ℂ) → ℝ),
      ShortFamily E lam → -((bundleRank E : ℝ) * meanLog K lam) ≤ bundleDegree E)

section HadExamples

variable (K : Type*) [Field K] [NumberField K]

/- English proof (translation)
Establish `h` using `norm_fibreVec_sq (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)`. Rewrite `h` using `[HermitianMetric.standard_inner_single, Complex.one_re]`. Establish `h0` using `norm_nonneg (fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1))`. Establish `h1 : ‖fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)‖ = 1`. Use polynomial arithmetic with `[sq_nonneg (‖fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)‖ - 1)]`.

Conclude with `h1`.
-/
theorem fibreNorm_standard_single (n : ℕ) (σ : K →+* ℂ) (i : Fin n) :
    fibreNorm (HermitianBundle.standard K n) σ ((1 : ComplexAt σ) ⊗ₜ[𝓞 K] Pi.single i 1) = 1 := by
  have h := norm_fibreVec_sq (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)
  rw [HermitianMetric.standard_inner_single, Complex.one_re] at h
  have h0 := norm_nonneg (fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1))
  have h1 : ‖fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)‖ = 1 := by
    nlinarith [sq_nonneg (‖fibreVec (HermitianMetric.standard K (Fin n)) σ (Pi.single i 1)‖ - 1)]
  exact h1

/- English proof (translation)
The claim follows from `Module.finrank_fin_fun (𝓞 K)`.
-/
theorem bundleRank_standard (n : ℕ) : bundleRank (HermitianBundle.standard K n) = n :=
  Module.finrank_fin_fun (𝓞 K)

def ShortFamily.standard (n : ℕ) : ShortFamily (HermitianBundle.standard K n) (fun _ ↦ 1) where
  vec i := (Pi.basisFun (𝓞 K) (Fin n) (Fin.cast (bundleRank_standard K n) i) : Fin n → 𝓞 K)
  linearIndependent :=
    (Pi.basisFun (𝓞 K) (Fin n)).linearIndependent.comp _ (Fin.cast_injective _)
  norm_le σ i := by
    rw [Pi.basisFun_apply]
    exact (fibreNorm_standard_single K n σ _).le

variable {K} in

def BoundedInjection.id (E : HermitianBundle K) : BoundedInjection E E (fun _ ↦ 1) where
  toLinearMap := LinearMap.id
  injective := Function.injective_id
  norm_le σ x := by rw [LinearMap.lTensor_id, LinearMap.id_apply, one_mul]

/- English proof (translation)
The claim follows from `BoundedInjection.id _`.
-/
example : BoundedInjection (ratStandard 2) (ratStandard 2) (fun _ ↦ 1) := BoundedInjection.id _
/- English proof (translation)
The claim follows from `ShortFamily.standard ℚ 2`.
-/
example : ShortFamily (ratStandard 2) (fun _ ↦ 1) := ShortFamily.standard ℚ 2

/- English proof (translation)
The claim follows from `BoundedInjection.id _`.
-/
example : BoundedInjection (gaussianStandard 2) (gaussianStandard 2) (fun _ ↦ 1) :=
  BoundedInjection.id _
/- English proof (translation)
The claim follows from `ShortFamily.standard GaussianField 2`.
-/
example : ShortFamily (gaussianStandard 2) (fun _ ↦ 1) := ShortFamily.standard GaussianField 2

/- English proof (translation)
The claim follows from `bundleRank_standard GaussianField 2`.
-/
example : bundleRank (gaussianStandard 2) = 2 := bundleRank_standard GaussianField 2

end HadExamples

def LogDetDerivative.Statement : Prop :=
  ∀ (m : ℕ) (G G' : ℝ → Matrix (Fin m) (Fin m) ℂ), (∀ t, (G t).PosDef) →
    (∀ t i j, HasDerivAt (fun s ↦ G s i j) (G' t i j) t) →
    ∀ t, HasDerivAt (fun s ↦ -(1 / 2) * Real.log (G s).det.re)
      (-(1 / 2) * ((G t)⁻¹ * G' t).trace.re) t

/- English proof (translation)
Use `⟨fun t ↦ PosDef.diagonal fun _ ↦ Complex.zero_lt_real.mpr (Real.exp_pos t), fun t i j ↦ ?_⟩` and prove the remaining obligations. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [diagonal_apply_eq]`. Conclude with `(Real.hasDerivAt_exp t).ofReal_comp`.

Simplify using `only [diagonal_apply_ne _ hij]`. Conclude with `hasDerivAt_const t 0`.
-/
theorem logDet_example :
    (∀ t : ℝ, (diagonal fun _ : Fin 2 ↦ ((Real.exp t : ℝ) : ℂ)).PosDef) ∧
    ∀ (t : ℝ) (i j : Fin 2),
      HasDerivAt (fun s : ℝ ↦ diagonal (fun _ : Fin 2 ↦ ((Real.exp s : ℝ) : ℂ)) i j)
        (diagonal (fun _ : Fin 2 ↦ ((Real.exp t : ℝ) : ℂ)) i j) t := by
  refine ⟨fun t ↦ PosDef.diagonal fun _ ↦ Complex.zero_lt_real.mpr (Real.exp_pos t),
    fun t i j ↦ ?_⟩
  by_cases hij : i = j
  · subst hij
    simp only [diagonal_apply_eq]
    exact (Real.hasDerivAt_exp t).ofReal_comp
  · simp only [diagonal_apply_ne _ hij]
    exact hasDerivAt_const t 0

def BetaSum.Statement : Prop :=
  ∀ D i : ℕ, i ≤ D →
    ∫ t in (0 : ℝ)..1, (D.choose i : ℝ) * t ^ i * (1 - t) ^ (D - i) = 1 / ((D : ℝ) + 1)

def GridSum.Statement : Prop :=
  ∀ D i : ℕ, i ≤ D →
    (fun n : ℕ ↦ (∑ a ∈ Finset.range n,
        (a : ℝ) ^ i * ((n - 1 - a : ℕ) : ℝ) ^ (D - i) / ((i.factorial : ℝ) * ((D - i).factorial : ℝ))) -
      (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) =O[atTop] fun n : ℕ ↦ (n : ℝ) ^ D

/- English proof (translation)
Evaluate the numerical expressions.
-/
example : (1 : ℕ) ≤ 2 := by norm_num

def Halving.Statement : Prop :=
  ∀ a : ℕ → ℝ, (∃ C : ℝ, ∀ n, |a n| ≤ C) →
    Tendsto (fun n ↦ a (2 * n) - a n / 2) atTop (𝓝 0) →
    Tendsto (fun n ↦ a (n + 1) - a n) atTop (𝓝 0) → Tendsto a atTop (𝓝 0)

/- English proof (translation)
Establish `h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0)` using `tendsto_one_div_add_atTop_nhds_zero_nat`. Use `⟨⟨1, fun n ↦ ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Establish `hn : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`. Rewrite using `[abs_of_pos (by positivity), div_le_one hn]`. Combine the linear relations using `[(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]`.

Establish `h2` using `h0.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))`. Simplify using `using h2.sub (h0.div_const 2)`. Establish `h1` using `h0.comp (tendsto_add_atTop_nat 1)`. Simplify using `using h1.sub h0`.
-/
theorem halving_example :
    (∃ C : ℝ, ∀ n : ℕ, |1 / ((n : ℝ) + 1)| ≤ C) ∧
    Tendsto (fun n : ℕ ↦ 1 / (((2 * n : ℕ) : ℝ) + 1) - 1 / ((n : ℝ) + 1) / 2) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) + 1) - 1 / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨⟨1, fun n ↦ ?_⟩, ?_, ?_⟩
  · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [abs_of_pos (by positivity), div_le_one hn]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  · have h2 := h0.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    simpa using h2.sub (h0.div_const 2)
  · have h1 := h0.comp (tendsto_add_atTop_nat 1)
    simpa using h1.sub h0

def unitBallVolume (R : ℕ) : ℝ := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin R)) 1)).toReal

structure ShortLatticeBasis {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (La : Submodule ℤ V) (c : ℝ) where

  vec : Fin (Module.finrank ℝ V) → V
  mem : ∀ i, vec i ∈ La
  linearIndependent : LinearIndependent ℝ vec
  norm_le : ∀ i, ‖vec i‖ ≤ c

def LatticeCount.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (La : Submodule ℤ V) [DiscreteTopology La]
    [IsZLattice ℝ La] (c b : ℝ), ShortLatticeBasis La c → 0 ≤ b →
      {x : V | x ∈ La ∧ ‖x‖ ≤ b}.Finite ∧
      ({x : V | x ∈ La ∧ ‖x‖ ≤ b}.ncard : ℝ) * ZLattice.covolume La ≤
        unitBallVolume (Module.finrank ℝ V) *
          (b + (Module.finrank ℝ V : ℝ) * c) ^ Module.finrank ℝ V

def SmallBallVolume.Statement : Prop := ∀ R : ℕ, unitBallVolume R ≤ 6

def MinkowskiCount.Statement : Prop :=
  (∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (La : Submodule ℤ V) [DiscreteTopology La]
    [IsZLattice ℝ La] (ρ : ℝ), 0 < ρ →
      Real.log (unitBallVolume (Module.finrank ℝ V)) +
          (Module.finrank ℝ V : ℝ) * Real.log (ρ / 2) - Real.log (ZLattice.covolume La) ≤
        Real.log ({x : V | x ∈ La ∧ ‖x‖ ≤ ρ}.ncard : ℝ)) ∧
  ∀ R : ℕ, (2 / Real.sqrt R) ^ R ≤ unitBallVolume R

def Packing.Statement : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (La : Submodule ℤ V) [Module.Finite ℤ La]
    (S : Finset V) (b : ℝ), 0 ≤ b → (∀ s ∈ S, s ∈ La) → (∀ s ∈ S, ‖s‖ ≤ 1) →
    (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Real.exp (-b) ≤ ‖s - t‖) →
      Real.log S.card ≤ Module.finrank ℤ La * (b + Real.log 3)

section LatticeExamples

def standardLattice : Submodule ℤ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)

instance : DiscreteTopology standardLattice := by
  unfold standardLattice; infer_instance

instance : IsZLattice ℝ standardLattice := by
  unfold standardLattice; infer_instance

instance : Module.Finite ℤ standardLattice := by
  unfold standardLattice; infer_instance

def ShortLatticeBasis.standard : ShortLatticeBasis standardLattice 1 where
  vec i := EuclideanSpace.basisFun (Fin 2) ℝ (Fin.cast finrank_euclideanSpace_fin i)
  mem i := Submodule.subset_span ⟨Fin.cast finrank_euclideanSpace_fin i, by simp⟩
  linearIndependent :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.linearIndependent.comp _ (Fin.cast_injective _)
  norm_le i := ((EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.1 _).le

/- English proof (translation)
Establish `hn : ‖EuclideanSpace.basisFun (Fin 2) ℝ 0‖ = 1` using `(EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.1 0`. Establish `hne : (0 : EuclideanSpace ℝ (Fin 2)) ≠ EuclideanSpace.basisFun (Fin 2) ℝ 0`. Introduce `h`. Rewrite `hn` using `[← h, norm_zero]`. Conclude with `zero_ne_one hn`.

Establish `hmem : EuclideanSpace.basisFun (Fin 2) ℝ 0 ∈ standardLattice` using `Submodule.subset_span ⟨0, by simp⟩`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s hs`. Break down `Finset.mem_insert.mp hs with rfl | hs` into its components or cases. Conclude with `Submodule.zero_mem _`.

Rewrite using `[Finset.mem_singleton.mp hs]`. Conclude with `hmem`. Introduce `s hs`. Break down `Finset.mem_insert.mp hs with rfl | hs` into its components or cases. Simplify using the standard rewrite rules.

Rewrite using `[Finset.mem_singleton.mp hs, hn]`. Introduce `s hs t ht hst`. Rewrite using `[neg_zero, Real.exp_zero]`. Apply the tactic sequence `rcases Finset.mem_insert.mp hs with rfl | hs <;> rcases Finset.mem_insert.mp ht with rfl | ht`. Conclude with `absurd rfl hst`.

Rewrite using `[Finset.mem_singleton.mp ht, zero_sub, norm_neg, hn]`. Rewrite using `[Finset.mem_singleton.mp hs, sub_zero, hn]`. Rewrite `hst` using `[Finset.mem_singleton.mp hs, Finset.mem_singleton.mp ht]`. Conclude with `absurd rfl hst`. Conclude with `Finset.card_pair hne`.
-/
theorem packing_example :
    let S : Finset (EuclideanSpace ℝ (Fin 2)) := {0, EuclideanSpace.basisFun (Fin 2) ℝ 0}
    (∀ s ∈ S, s ∈ standardLattice) ∧ (∀ s ∈ S, ‖s‖ ≤ 1) ∧
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t → Real.exp (-0) ≤ ‖s - t‖) ∧ S.card = 2 := by
  have hn : ‖EuclideanSpace.basisFun (Fin 2) ℝ 0‖ = 1 :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal.1 0
  have hne : (0 : EuclideanSpace ℝ (Fin 2)) ≠ EuclideanSpace.basisFun (Fin 2) ℝ 0 := by
    intro h; rw [← h, norm_zero] at hn; exact zero_ne_one hn
  have hmem : EuclideanSpace.basisFun (Fin 2) ℝ 0 ∈ standardLattice :=
    Submodule.subset_span ⟨0, by simp⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact Submodule.zero_mem _
    · rw [Finset.mem_singleton.mp hs]; exact hmem
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · simp
    · rw [Finset.mem_singleton.mp hs, hn]
  · intro s hs t ht hst
    rw [neg_zero, Real.exp_zero]
    rcases Finset.mem_insert.mp hs with rfl | hs <;> rcases Finset.mem_insert.mp ht with rfl | ht
    · exact absurd rfl hst
    · rw [Finset.mem_singleton.mp ht, zero_sub, norm_neg, hn]
    · rw [Finset.mem_singleton.mp hs, sub_zero, hn]
    · rw [Finset.mem_singleton.mp hs, Finset.mem_singleton.mp ht] at hst; exact absurd rfl hst
  · exact Finset.card_pair hne

end LatticeExamples

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
