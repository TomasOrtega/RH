import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryTopology

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.PetPos

/- English proof (translation)
Establish `hre : ∀ h, (star (φ h) * φ h).re = Complex.normSq (φ h)` using `fun h => by`. Simplify using `[Complex.normSq_apply]`. Establish `e1 : (∫ h in 𝓕, star (φ h) * φ h ∂μ).re = ∫ h in 𝓕, Complex.normSq (φ h) ∂μ`. Use `integral_re (𝕜 := ℂ) hi` as an intermediate fact. Simplify using `only [RCLike.re_to_complex, hre] at this`.

Conclude with `this.symm`. Establish `hi' : IntegrableOn (fun h => Complex.normSq (φ h)) 𝓕 μ`. Use `Integrable.re (𝕜 := ℂ) hi` as an intermediate fact. Simplify using `only [RCLike.re_to_complex, hre] at this`. Conclude with `this`.

Rewrite using `[e1, setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun h => Complex.normSq_nonneg _) hi']`. Establish `hs : Function.support (fun h => Complex.normSq (φ h)) = Function.support φ`. Use extensionality with `h`. Simplify using `[Function.mem_support]`. Rewrite using `[hs, pos_iff_ne_zero]`.

Introduce `hz`. Establish `hinv : ∀ γ : Γ, γ • Function.support φ = Function.support φ` using `fun γ => by`. Use extensionality with `g`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]`. Establish `: φ (γ⁻¹ • g) = φ g` using `hl _ (γ⁻¹).2 g`.

Rewrite using `[this]`. Establish `hzero` using `h𝓕.measure_zero_of_invariant _ hinv hz`. Conclude with `(hc.isOpen_support.measure_pos μ (Function.support_nonempty_iff.2 h0)).ne' hzero`.
-/
theorem sq_integral_pos {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsOpenPosMeasure] (𝓕 : Set G)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (φ : G → ℂ) (hl : ∀ γ ∈ Γ, ∀ g, φ (γ * g) = φ g) (hc : Continuous φ) (h0 : φ ≠ 0)
    (hi : IntegrableOn (fun h => star (φ h) * φ h) 𝓕 μ) : 0 < (∫ h in 𝓕, star (φ h) * φ h ∂μ).re := by
  have hre : ∀ h, (star (φ h) * φ h).re = Complex.normSq (φ h) := fun h => by
    simp [Complex.normSq_apply]
  have e1 : (∫ h in 𝓕, star (φ h) * φ h ∂μ).re = ∫ h in 𝓕, Complex.normSq (φ h) ∂μ := by
    have := integral_re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, hre] at this
    exact this.symm
  have hi' : IntegrableOn (fun h => Complex.normSq (φ h)) 𝓕 μ := by
    have := Integrable.re (𝕜 := ℂ) hi
    simp only [RCLike.re_to_complex, hre] at this
    exact this
  rw [e1, setIntegral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall fun h => Complex.normSq_nonneg _) hi']
  have hs : Function.support (fun h => Complex.normSq (φ h)) = Function.support φ := by
    ext h
    simp [Function.mem_support]
  rw [hs, pos_iff_ne_zero]
  intro hz
  have hinv : ∀ γ : Γ, γ • Function.support φ = Function.support φ := fun γ => by
    ext g
    rw [Set.mem_smul_set_iff_inv_smul_mem, Function.mem_support, Function.mem_support]
    have : φ (γ⁻¹ • g) = φ g := hl _ (γ⁻¹).2 g
    rw [this]
  have hzero := h𝓕.measure_zero_of_invariant _ hinv hz
  exact (hc.isOpen_support.measure_pos μ (Function.support_nonempty_iff.2 h0)).ne' hzero

/- English proof (translation)
Introduce `D V μ 𝓕 hq φ hφ h0 hi`. Take `⟨-, -, -, h4, h5, -, h7⟩` from `GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V`. Establish `hH` using `hq.1`. Conclude with `sq_integral_pos (GQ V) μ 𝓕 hq.2 φ hφ.left hφ.cont h0 hi`.
-/
theorem petersson_pos : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)), IsQuot V μ 𝓕 → ∀ φ, IsAutFun V φ → φ ≠ 0 → IntegrableOn (fun h => star (φ h) * φ h) 𝓕 μ → 0 < (∫ h in 𝓕, star (φ h) * φ h ∂μ).re := by
  intro D V μ 𝓕 hq φ hφ h0 hi
  obtain ⟨-, -, -, h4, h5, -, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have hH := hq.1
  exact sq_integral_pos (GQ V) μ 𝓕 hq.2 φ hφ.left hφ.cont h0 hi

end GlobalTheory.Mem.PetPos
