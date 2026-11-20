import Mathlib
import GroundTheory.AutomorphicForms.WhittakerDistribution
import GroundTheory.AutomorphicForms.WhittakerCriterion
import GroundTheory.AutomorphicForms.MeasuresGL

namespace GroundTheory.Automorphic

namespace Whittaker

open MeasureTheory Measure ValuativeRel

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

/- English proof (translation)
Introduce `D hD f`. Establish `key` using `distribution_sigma_invariant ψ₀ hψ hψ₁ D (fun f u₁ u₂ hu₁ hu₂ => by`. Establish `e : (⟨fun x => (f : GL (Fin n) F → ℂ) (u₁⁻¹ * x * u₂), twoSided_mem f.2 u₁ u₂⟩ : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = biTranslL u₁ u₂ f` using `Subtype.ext (coe_biTranslL u₁ u₂ f).symm`. Rewrite using `[e]`. Conclude with `hD f ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩) f`.

Establish `e : compHomeoL sigmaHomeo f = (⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ : locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ)` using `Subtype.ext rfl`. Rewrite using `[e]`. Conclude with `key`.
-/
theorem biEquivariantSigmaInvariant_GL (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) :
    BiEquivariantSigmaInvariant (Iwasawa.unipotent F n)
      (fun u => psiN ψ₀ (u : GL (Fin n) F)) sigmaHomeo := by
  intro D hD f
  have key := distribution_sigma_invariant ψ₀ hψ hψ₁ D (fun f u₁ u₂ hu₁ hu₂ => by
    have e : (⟨fun x => (f : GL (Fin n) F → ℂ) (u₁⁻¹ * x * u₂), twoSided_mem f.2 u₁ u₂⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) = biTranslL u₁ u₂ f :=
      Subtype.ext (coe_biTranslL u₁ u₂ f).symm
    rw [e]
    exact hD f ⟨u₁, hu₁⟩ ⟨u₂, hu₂⟩) f
  have e : compHomeoL sigmaHomeo f =
      (⟨fun x => (f : GL (Fin n) F → ℂ) (sigma x), comp_sigma_mem f.2⟩ :
        locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) := Subtype.ext rfl
  rw [e]
  exact key

section Measure

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]

def thetaEquiv : GL (Fin n) F ≃* GL (Fin n) F where
  toFun := theta
  invFun := theta
  left_inv := theta_theta
  right_inv := theta_theta
  map_mul' := theta_mul

/- English proof (translation)
Establish `hθc : Continuous (theta : GL (Fin n) F → GL (Fin n) F)` using `continuous_theta`. Establish `hθm : Measurable (theta : GL (Fin n) F → GL (Fin n) F)` using `hθc.measurable`. Establish `: (μ.map theta).IsHaarMeasure` using `MulEquiv.isHaarMeasure_map μ (thetaEquiv (F := F) (n := n)) hθc hθc`. Use `set c := haarScalarFactor (μ.map theta) μ`. Establish `e : μ.map theta = c • μ` using `isMulLeftInvariant_eq_smul (μ.map theta) μ`.

Establish `e2 : μ = (c * c) • μ`. Establish `h1 : (μ.map theta).map theta = μ`. Rewrite using `[Measure.map_map hθm hθm]`. Establish `: (theta ∘ theta : GL (Fin n) F → GL (Fin n) F) = id` using `funext theta_theta`. Rewrite using `[this, Measure.map_id]`.

Establish `h2 : (μ.map theta).map theta = (c * c) • μ`. Rewrite using `[e, Measure.map_smul, e, smul_smul]`. Conclude with `h1.symm.trans h2`. Use `set K := GLnLocal.integralGL F n`. Establish `hK0 : μ K ≠ 0` using `(GLnLocal.isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩`.

Establish `hKT : μ K ≠ ⊤` using `(GLnLocal.isCompact_integralGL F n).measure_lt_top.ne`. Establish `hc : c = 1`. Establish `h` using `congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e2`. Simplify using `only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h`. Establish `h'` using `(ENNReal.mul_eq_right hK0 hKT).1 h.symm`.

Establish `hcc : (c * c : NNReal) = 1` using `by exact_mod_cast h'`. Establish `hr : ((c : ℝ) * (c : ℝ)) = 1` using `by exact_mod_cast hcc`. Establish `hc0 : (0 : ℝ) ≤ c` using `c.2`. Establish `: (c : ℝ) = 1` using `by nlinarith`. Conclude with `this` after adjusting the coercions.

Establish `eθ : μ.map theta = μ` using `by rw [e, hc, one_smul]`. Establish `hσ : (sigma : GL (Fin n) F → GL (Fin n) F) = (fun g => g⁻¹) ∘ theta`. Use function extensionality and compare the values at `g`. Simplify using `[theta]`. Rewrite using `[hσ, ← Measure.map_map continuous_inv.measurable hθm, eθ]`.

Conclude with `Measures.inv_eq_self_GL F n μ`.
-/
theorem map_sigma_eq (μ : Measure (GL (Fin n) F)) [μ.IsHaarMeasure] : μ.map sigma = μ := by
  have hθc : Continuous (theta : GL (Fin n) F → GL (Fin n) F) := continuous_theta
  have hθm : Measurable (theta : GL (Fin n) F → GL (Fin n) F) := hθc.measurable
  have : (μ.map theta).IsHaarMeasure :=
    MulEquiv.isHaarMeasure_map μ (thetaEquiv (F := F) (n := n)) hθc hθc
  set c := haarScalarFactor (μ.map theta) μ
  have e : μ.map theta = c • μ := isMulLeftInvariant_eq_smul (μ.map theta) μ
  have e2 : μ = (c * c) • μ := by
    have h1 : (μ.map theta).map theta = μ := by
      rw [Measure.map_map hθm hθm]
      have : (theta ∘ theta : GL (Fin n) F → GL (Fin n) F) = id := funext theta_theta
      rw [this, Measure.map_id]
    have h2 : (μ.map theta).map theta = (c * c) • μ := by
      rw [e, Measure.map_smul, e, smul_smul]
    exact h1.symm.trans h2
  set K := GLnLocal.integralGL F n
  have hK0 : μ K ≠ 0 := (GLnLocal.isOpen_integralGL F n).measure_ne_zero μ ⟨1, K.one_mem⟩
  have hKT : μ K ≠ ⊤ := (GLnLocal.isCompact_integralGL F n).measure_lt_top.ne
  have hc : c = 1 := by
    have h := congrArg (fun ν : Measure (GL (Fin n) F) => ν K) e2
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    have h' := (ENNReal.mul_eq_right hK0 hKT).1 h.symm
    have hcc : (c * c : NNReal) = 1 := by exact_mod_cast h'
    have hr : ((c : ℝ) * (c : ℝ)) = 1 := by exact_mod_cast hcc
    have hc0 : (0 : ℝ) ≤ c := c.2
    have : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast this
  have eθ : μ.map theta = μ := by rw [e, hc, one_smul]
  have hσ : (sigma : GL (Fin n) F → GL (Fin n) F) = (fun g => g⁻¹) ∘ theta := by
    funext g
    simp [theta]
  rw [hσ, ← Measure.map_map continuous_inv.measurable hθm, eθ]
  exact Measures.inv_eq_self_GL F n μ

end Measure

/- English proof (translation)
Set `_ : MeasurableSpace (GL (Fin n) F)` to `_root_.borel _`. Establish `: BorelSpace (GL (Fin n) F)` using `⟨rfl⟩`. Establish `: (haar : Measure (GL (Fin n) F)).IsInvInvariant` using `⟨Measures.inv_eq_self_GL F n _⟩`. Conclude with `rank_mul_rank_le_one (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo) (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ`.
-/
theorem rank_whittaker_mul_rank_whittaker_contragredient_le_one (ψ₀ : AddChar F ℂ)
    (hψ : Continuous ψ₀) (hψ₁ : ψ₀ ≠ 1) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible] :
    Module.rank ℂ (equivariantFunctionals π
        (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) *
      Module.rank ℂ (equivariantFunctionals (contragredient π)
        (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹)) ≤ 1 := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  have : (haar : Measure (GL (Fin n) F)).IsInvInvariant := ⟨Measures.inv_eq_self_GL F n _⟩
  exact rank_mul_rank_le_one (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo)
    (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ

/- English proof (translation)
Set `_ : MeasurableSpace (GL (Fin n) F)` to `_root_.borel _`. Establish `: BorelSpace (GL (Fin n) F)` using `⟨rfl⟩`. Establish `: (haar : Measure (GL (Fin n) F)).IsInvInvariant` using `⟨Measures.inv_eq_self_GL F n _⟩`. Conclude with `rank_le_one_of_ne_bot (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo) (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ hne`.
-/
theorem rank_whittaker_le_one_of_contragredient (ψ₀ : AddChar F ℂ) (hψ : Continuous ψ₀)
    (hψ₁ : ψ₀ ≠ 1) {V : Type*} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) F) V) (hπ : IsAdmissible π) [π.IsIrreducible]
    (hne : equivariantFunctionals (contragredient π)
      (fun u : Iwasawa.unipotent F n => (psiN ψ₀ (u : GL (Fin n) F))⁻¹) ≠ ⊥) :
    Module.rank ℂ (equivariantFunctionals π
      (fun u : Iwasawa.unipotent F n => psiN ψ₀ (u : GL (Fin n) F))) ≤ 1 := by
  let _ : MeasurableSpace (GL (Fin n) F) := _root_.borel _
  have : BorelSpace (GL (Fin n) F) := ⟨rfl⟩
  have : (haar : Measure (GL (Fin n) F)).IsInvInvariant := ⟨Measures.inv_eq_self_GL F n _⟩
  exact rank_le_one_of_ne_bot (haar : Measure (GL (Fin n) F)) (σ := sigmaHomeo)
    (fun x y => sigma_mul x y) (map_sigma_eq _) (biEquivariantSigmaInvariant_GL ψ₀ hψ hψ₁) hπ hne

end Whittaker

end GroundTheory.Automorphic
