import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RatVInjective
import GroundTheory.AutomorphicForms.AnisotropicUnitaryCompact
import CompanionTheory.AutomorphicTheory.SiegelWeilFiniteness.Bridge

set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RedCov
open Formalism.UG (cT)
open scoped TensorProduct NNReal ENNReal NumberField.AdeleRing
open GroundTheory.Automorphic GroundTheory.Automorphic.Anisotropic

namespace GlobalTheory.CompanionTheory.RedCov.Bridge

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

variable (F E n) in

abbrev dimN : ℕ := Fintype.card (Fin n × Fin (Module.finrank F E))

def trG : GAd σ J →* GL (Fin (dimN F E n)) (AF F) :=
  (trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (matHom (AF F) σ J)

variable (F) in

def cvec (v : Fin n → E) : Fin (dimN F E n) → F := fun p =>
  (Module.finBasis F E).repr (v ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).1)
    ((Fintype.equivFin (Fin n × Fin (Module.finrank F E))).symm p).2

/- English proof (translation)
Introduce `u v h`. Use function extensionality and compare the values at `i`. Apply `(Module.finBasis F E).repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Simplify `congrFun h (Fintype.equivFin (Fin n × Fin (Module.finrank F E)) (i, k))` using `[cvec]`.
-/
theorem cvec_injective : Function.Injective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro u v h
  funext i
  apply (Module.finBasis F E).repr.injective
  ext k
  simpa [cvec] using congrFun h (Fintype.equivFin (Fin n × Fin (Module.finrank F E)) (i, k))

/- English proof (translation)
Introduce `x`. Use `⟨fun i => (Module.finBasis F E).equivFun.symm fun k => x (Fintype.equivFin _ (i, k)), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Simplify using `[cvec, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]`.
-/
theorem cvec_surjective : Function.Surjective (cvec F : (Fin n → E) → Fin (dimN F E n) → F) := by
  intro x
  refine ⟨fun i => (Module.finBasis F E).equivFun.symm fun k => x (Fintype.equivFin _ (i, k)), ?_⟩
  funext p
  simp [cvec, Module.Basis.equivFun_symm_apply, Finsupp.single_apply]

/- English proof (translation)
Introduce `h`. Apply `hv` to reduce the goal to its premises. Apply `cvec_injective (F := F)` to reduce the goal to its premises. Rewrite using `[h]`. Use function extensionality and compare the values at `p`.

Simplify using `[cvec]`.
-/
theorem cvec_ne_zero {v : Fin n → E} (hv : v ≠ 0) : cvec F v ≠ 0 := by
  intro h
  apply hv
  apply cvec_injective (F := F)
  rw [h]
  funext p
  simp [cvec]

/- English proof (translation)
Use function extensionality and compare the values at `p`. Simplify using `only [Reduction.ratVec, cvec, resVec, Function.comp_apply, coordsVec, coords, ratV, inclR]`. Simplify using `[Algebra.TensorProduct.basis_repr_tmul]`.
-/
theorem ratVec_cvec (v : Fin n → E) :
    Reduction.ratVec (cvec F v) = resVec (ι := Fin n) (Module.finBasis F E) (AF F) (ratV F v) := by
  funext p
  simp only [Reduction.ratVec, cvec, resVec, Function.comp_apply, coordsVec, coords, ratV, inclR]
  simp [Algebra.TensorProduct.basis_repr_tmul]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem hv_eq (ξ : Fin n → AF F ⊗[F] E) :
    hv ξ = Reduction.adelicNorm (resVec (ι := Fin n) (Module.finBasis F E) (AF F) ξ) := rfl

/- English proof (translation)
Rewrite using `[Reduction.height, ratVec_cvec, trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hgt, hv_eq, map_inv]`.
-/
theorem hgt_eq (g : GAd σ J) (v : Fin n → E) : hgt σ J g v = Reduction.height (trG σ J g) (cvec F v) := by
  rw [Reduction.height, ratVec_cvec, trG, MonoidHom.comp_apply, resVec_vecMul_trHom, hgt, hv_eq, map_inv]

section Top

attribute [local instance] tensorTopology finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

/- English proof (translation)
The claim follows from `(continuous_trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (isEmbedding_matHom (AF F) σ J).continuous`.
-/
theorem continuous_trG : Continuous (trG σ J) :=
  (continuous_trHom (ι := Fin n) (Module.finBasis F E) (AF F)).comp (isEmbedding_matHom (AF F) σ J).continuous

end Top

/- English proof (translation)
Take `⟨P, -, hP⟩` from `Reduction.exists_adelicNorm_vecMul_le_mul (hC.image (continuous_trG σ J))`. Use `⟨P * Reduction.adelicNorm (Reduction.ratVec (cvec F v)), fun c hc => ?_⟩` and prove the remaining obligations. Rewrite using `[hgt_eq]`. Conclude with `hP _ ⟨c, hc, rfl⟩ _ (Reduction.hasFiniteContent_ratVec (cvec_ne_zero hv))`.
-/
theorem exists_hgt_le {C : Set (GAd σ J)} (hC : IsCompact C) {v : Fin n → E} (hv : v ≠ 0) :
    ∃ B : ℝ, ∀ c ∈ C, hgt σ J c v ≤ B := by
  obtain ⟨P, -, hP⟩ := Reduction.exists_adelicNorm_vecMul_le_mul (hC.image (continuous_trG σ J))
  refine ⟨P * Reduction.adelicNorm (Reduction.ratVec (cvec F v)), fun c hc => ?_⟩
  rw [hgt_eq]
  exact hP _ ⟨c, hc, rfl⟩ _ (Reduction.hasFiniteContent_ratVec (cvec_ne_zero hv))

end GlobalTheory.CompanionTheory.RedCov.Bridge
