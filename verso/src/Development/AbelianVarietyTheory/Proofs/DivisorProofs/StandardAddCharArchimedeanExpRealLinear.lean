import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceVecPairAsAdeles
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IteratedLineDerivMemWeylAlg

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdCharLin

/- English proof (translation)
Use `continuous_pi fun v => ?_` and prove the remaining obligations. Break down `v.isReal_or_isComplex with hv | hv` into its components or cases. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]`. Conclude with `((continuous_apply _).comp continuous_fst).congr fun y => (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm`. Rewrite using `[(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]`.

Conclude with `((continuous_apply _).comp continuous_snd).congr fun y => (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm`.
-/
theorem continuous_ofMixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm := by
  refine continuous_pi fun v => ?_
  rcases v.isReal_or_isComplex with hv | hv
  · rw [(InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hv).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_fst).congr fun y =>
      (congrFun (congrArg Prod.fst ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm
  · rw [(InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.continuous_iff]
    exact ((continuous_apply _).comp continuous_snd).congr fun y =>
      (congrFun (congrArg Prod.snd ((InfiniteAdeleRing.ringEquiv_mixedSpace F).apply_symm_apply y)) ⟨v, hv⟩).symm

/- English proof (translation)
Introduce `D ψ θ hψ hθ`. Take `⟨hc, hall⟩` from `hψ`. Establish `key` using `hall.2 θ hθ`. Use `set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F with he`. Set `z : Ainf D.host.F → ℂ` to `fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))`.

Establish `hkey : ∀ x, ψ ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F) = Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x)` using `fun x => key x`. Establish `him : ∀ x, (z x).im = 0`. Introduce `x`. Establish `h1` using `hc.2.1 ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F)`. Rewrite `h1` using `[hkey x, Complex.norm_exp]`.

Establish `hre : (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x).re = 2 * Real.pi * (z x).im`. Simplify using `[Complex.mul_re, Complex.mul_im]`. Rewrite `h1` using `[hre, Real.exp_eq_one_iff]`. Establish `hp : (0 : ℝ) < 2 * Real.pi` using `by positivity`. Break down `mul_eq_zero.1 h1 with h | h` into its components or cases.

Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h`. Establish `hzadd : ∀ x y, z (x + y) = z x + z y`. Introduce `x y`. Simplify using `only [z, TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]`.

Set `g : mixedEmbedding.mixedSpace D.host.F →+ ℝ` to `{ toFun := fun a => -(z (e.symm a)).re map_zero' := by simp [z] map_add' := by intro a b; simp only [map_add, hzadd, Complex.add_re, neg_add] }`. Establish `hg : Continuous g`. Establish `: Continuous fun x : Ainf D.host.F => z x` using `continuous_finset_sum _ fun ρ _ => (hθ ρ).2`. Conclude with `(Complex.continuous_re.comp (this.comp (continuous_ofMixed D.host.F))).neg`. Use `⟨(g.toRealLinearMap hg : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ), ?_, fun a => rfl⟩` and prove the remaining obligations.

Introduce `a`. Establish `hz : z (e.symm a) = ((z (e.symm a)).re : ℂ)` using `Complex.ext rfl (by simp [him])`. Rewrite using `[hkey (e.symm a)]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = 2 * Real.pi * Complex.I * ((-(z (e.symm a)).re : ℝ) : ℂ)`.

Rewrite using `[hz]`. Use `push_cast`. Simplify using `only [Complex.ofReal_re]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stdChar_mixed_linear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ)
    (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsStdChar D ψ (-1) → IsInfFam θ →
    ∃ β : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ,
      (∀ a, ψ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
        Complex.exp (2 * Real.pi * Complex.I * β a)) ∧
      ∀ a, β a = -(∑ ρ, θ ρ (((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm a) ⊗ₜ[D.host.F]
        (1 : D.host.E))).re := by
  intro D ψ θ hψ hθ
  obtain ⟨hc, hall⟩ := hψ
  have key := hall.2 θ hθ
  set e := InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F with he
  let z : Ainf D.host.F → ℂ := fun x => ∑ ρ, θ ρ (x ⊗ₜ[D.host.F] (1 : D.host.E))
  have hkey : ∀ x, ψ ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F) =
      Complex.exp (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x) := fun x => key x
  have him : ∀ x, (z x).im = 0 := by
    intro x
    have h1 := hc.2.1 ((x, 0) : AdeleRing (𝓞 D.host.F) D.host.F)
    rw [hkey x, Complex.norm_exp] at h1
    have hre : (2 * Real.pi * Complex.I * ((-1 : ℤ) : ℂ) * z x).re = 2 * Real.pi * (z x).im := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_eq_one_iff] at h1
    have hp : (0 : ℝ) < 2 * Real.pi := by positivity
    rcases mul_eq_zero.1 h1 with h | h
    · linarith
    · exact h
  have hzadd : ∀ x y, z (x + y) = z x + z y := by
    intro x y
    simp only [z, TensorProduct.add_tmul, map_add, Finset.sum_add_distrib]
  let g : mixedEmbedding.mixedSpace D.host.F →+ ℝ :=
    { toFun := fun a => -(z (e.symm a)).re
      map_zero' := by simp [z]
      map_add' := by intro a b; simp only [map_add, hzadd, Complex.add_re, neg_add] }
  have hg : Continuous g := by
    have : Continuous fun x : Ainf D.host.F => z x :=
      continuous_finset_sum _ fun ρ _ => (hθ ρ).2
    exact (Complex.continuous_re.comp (this.comp (continuous_ofMixed D.host.F))).neg
  refine ⟨(g.toRealLinearMap hg : mixedEmbedding.mixedSpace D.host.F →ₗ[ℝ] ℝ), ?_, fun a => rfl⟩
  intro a
  have hz : z (e.symm a) = ((z (e.symm a)).re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hkey (e.symm a)]
  congr 1
  change _ = 2 * Real.pi * Complex.I * ((-(z (e.symm a)).re : ℝ) : ℂ)
  rw [hz]
  push_cast
  simp only [Complex.ofReal_re]
  ring

end GlobalTheory.StdCharLin
