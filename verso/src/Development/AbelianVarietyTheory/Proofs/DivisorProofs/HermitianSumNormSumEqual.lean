import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreConcl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLineReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLatticeZeroTorus
open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.EisRes GlobalTheory.EisRestrict
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CMNormSum

/- English proof (translation)
Use `h.1` as an intermediate fact. Establish `hr : w.IsReal` using `IsTotallyReal.isReal w`. Set `e : w.Completion ≃+* ℝ` to `InfinitePlace.Completion.ringEquivRealOfIsReal hr`. Establish `he : ∀ a, InfinitePlace.Completion.extensionEmbedding w a = ((e a : ℝ) : ℂ)` using `fun a => (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr a).symm`. Take `⟨τ⟩` from `(inferInstance : Nonempty (GlobalTheory.AdelicU.EmbOver E w))`.

Set `φ` to `GlobalTheory.AdelicU.infEmb τ`. Establish `hbij` using `GlobalTheory.AdelicU.infEmb_bijective h τ`. Establish `hφa : ∀ a : w.Completion, φ (algebraMap w.Completion (w.Completion ⊗[F] E) a) = ((e a : ℝ) : ℂ)`. Introduce `a`. Rewrite using `[Algebra.TensorProduct.algebraMap_apply]`.

Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply]`. Use `show GlobalTheory.AdelicU.infEmb τ (a ⊗ₜ[F] (1 : E)) = _`. Rewrite using `[GlobalTheory.AdelicU.infEmb_tmul, map_one, mul_one, he]`. Establish `hinj : Function.Injective (algebraMap w.Completion (w.Completion ⊗[F] E))`. Introduce `a b hab`.

Use `congrArg φ hab` as an intermediate fact. Rewrite `this` using `[hφa, hφa]`. Conclude with `e.injective (Complex.ofReal_injective this)`. Use `⟨fun t => ?_, hinj⟩` and prove the remaining obligations. Set `e₂ : w.Completion ⊗[F] E ≃+* ℂ` to `RingEquiv.ofBijective φ hbij`.

Establish `hN : Algebra.norm w.Completion t = e.symm (Algebra.norm ℝ (e₂ t))`. Use `Algebra.norm_eq_of_equiv_equiv e e₂ ?_ t` and prove the remaining obligations. Use extensionality with `a`. Simplify using `only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]`. Rewrite using `[show e₂ (algebraMap w.Completion (w.Completion ⊗[F] E) a) = φ (algebraMap _ _ a) from rfl, hφa]`.

Both sides reduce to the same expression. Apply `hbij.1` to reduce the goal to its premises. Rewrite using `[hφa, hN, e.apply_symm_apply, Algebra.norm_complex_apply, map_mul, ← GlobalTheory.AdelicU.infEmb_sigR h τ t]`. Use `show ((Complex.normSq (φ t) : ℝ) : ℂ) = starRingEnd ℂ (φ t) * φ t`. Rewrite using `[Complex.normSq_eq_conj_mul_self]`.
-/
theorem algebraMap_norm_and_inj (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (w : InfinitePlace F) :
    (∀ t : w.Completion ⊗[F] E,
      algebraMap w.Completion (w.Completion ⊗[F] E) (Algebra.norm w.Completion t) = sigR w.Completion σ t * t) ∧
    Function.Injective (algebraMap w.Completion (w.Completion ⊗[F] E)) := by
  have := h.1
  have hr : w.IsReal := IsTotallyReal.isReal w
  let e : w.Completion ≃+* ℝ := InfinitePlace.Completion.ringEquivRealOfIsReal hr
  have he : ∀ a, InfinitePlace.Completion.extensionEmbedding w a = ((e a : ℝ) : ℂ) :=
    fun a => (InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hr a).symm
  obtain ⟨τ⟩ := (inferInstance : Nonempty (GlobalTheory.AdelicU.EmbOver E w))
  let φ := GlobalTheory.AdelicU.infEmb τ
  have hbij := GlobalTheory.AdelicU.infEmb_bijective h τ
  have hφa : ∀ a : w.Completion, φ (algebraMap w.Completion (w.Completion ⊗[F] E) a) = ((e a : ℝ) : ℂ) := by
    intro a
    rw [Algebra.TensorProduct.algebraMap_apply]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
    show GlobalTheory.AdelicU.infEmb τ (a ⊗ₜ[F] (1 : E)) = _
    rw [GlobalTheory.AdelicU.infEmb_tmul, map_one, mul_one, he]
  have hinj : Function.Injective (algebraMap w.Completion (w.Completion ⊗[F] E)) := by
    intro a b hab
    have := congrArg φ hab
    rw [hφa, hφa] at this
    exact e.injective (Complex.ofReal_injective this)
  refine ⟨fun t => ?_, hinj⟩
  let e₂ : w.Completion ⊗[F] E ≃+* ℂ := RingEquiv.ofBijective φ hbij
  have hN : Algebra.norm w.Completion t = e.symm (Algebra.norm ℝ (e₂ t)) := by
    refine Algebra.norm_eq_of_equiv_equiv e e₂ ?_ t
    ext a
    simp only [RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [show e₂ (algebraMap w.Completion (w.Completion ⊗[F] E) a) = φ (algebraMap _ _ a) from rfl, hφa]
    rfl
  apply hbij.1
  rw [hφa, hN, e.apply_symm_apply, Algebra.norm_complex_apply, map_mul,
    ← GlobalTheory.AdelicU.infEmb_sigR h τ t]
  show ((Complex.normSq (φ t) : ℝ) : ℂ) = starRingEnd ℂ (φ t) * φ t
  rw [Complex.normSq_eq_conj_mul_self]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ h w k k' z z' hz`. Take `⟨hN, hinj⟩` from `algebraMap_norm_and_inj F E σ h w`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_sum, map_sum]`. Simplify using `only [hN]`.

Conclude with `hz`.
-/
theorem sum_norm_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (w : InfinitePlace F) (k k' : ℕ) (z : Fin k → w.Completion ⊗[F] E) (z' : Fin k' → w.Completion ⊗[F] E),
    ∑ i, sigR w.Completion σ (z i) * z i = ∑ i, sigR w.Completion σ (z' i) * z' i →
    ∑ i, Algebra.norm w.Completion (z i) = ∑ i, Algebra.norm w.Completion (z' i) := by
  intro F E _ _ _ _ _ σ h w k k' z z' hz
  obtain ⟨hN, hinj⟩ := algebraMap_norm_and_inj F E σ h w
  apply hinj
  rw [map_sum, map_sum]
  simp only [hN]
  exact hz

end GlobalTheory.CMNormSum
