import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocMInvMul
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling
open GlobalTheory.SWLit GlobalTheory.SWWeil GlobalTheory.SWACase GlobalTheory.SWLow GlobalTheory.SWMidF GlobalTheory.SWOpCase GlobalTheory.SWOpFin

namespace GlobalTheory.SWOpFin

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `Prod.ext (funext fun w => hi w) ?_` and prove the remaining obligations. Conclude with `Subtype.ext (funext fun v => hf v)`.
-/
theorem adele_eq_zero_of_comp {c : AF F} (hf : ∀ v, evFin F v c = 0) (hi : ∀ w, evInf F w c = 0) : c = 0 := by
  refine Prod.ext (funext fun w => hi w) ?_
  exact Subtype.ext (funext fun v => hf v)

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis F E`. Set `B` to `Algebra.TensorProduct.basis (AF F) b`. Establish `key : ∀ {A : Type} [CommRing A] [Algebra F A] (f : AF F →ₐ[F] A), (Algebra.TensorProduct.map f (AlgHom.id F E)) z = 0 → ∀ i, f (B.repr z i) = 0`. Introduce `A _ _ f hz i`. Establish `hs : z = ∑ j, B.repr z j • B j` using `(B.sum_repr z).symm`.

Establish `hz' : ∑ j, f (B.repr z j) • (Algebra.TensorProduct.basis A b) j = 0`. Rewrite `hz` using `[hs]`. Simplify `hz` using `[B, Algebra.TensorProduct.basis_apply, Finset.sum_apply, map_sum, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Algebra.TensorProduct.map_tmul]`. Conclude with `Fintype.linearIndependent_iff.1 (Algebra.TensorProduct.basis A b).linearIndependent _ hz' i`. Establish `hc : ∀ i, B.repr z i = 0` using `fun i => adele_eq_zero_of_comp (fun v => key (evFin F v) (hf v) i) (fun w => key (evInf F w) (hi w) i)`.

Rewrite using `[← B.sum_repr z]`. Simplify using `[hc]`.
-/
theorem tens_eq_zero_of_comp {z : AF F ⊗[F] E} (hf : ∀ v, compFin F E v z = 0) (hi : ∀ w, compInf F E w z = 0) :
    z = 0 := by
  let b := Module.Free.chooseBasis F E
  let B := Algebra.TensorProduct.basis (AF F) b
  have key : ∀ {A : Type} [CommRing A] [Algebra F A] (f : AF F →ₐ[F] A),
      (Algebra.TensorProduct.map f (AlgHom.id F E)) z = 0 → ∀ i, f (B.repr z i) = 0 := by
    intro A _ _ f hz i
    have hs : z = ∑ j, B.repr z j • B j := (B.sum_repr z).symm
    have hz' : ∑ j, f (B.repr z j) • (Algebra.TensorProduct.basis A b) j = 0 := by
      rw [hs] at hz
      simpa [B, Algebra.TensorProduct.basis_apply, Finset.sum_apply, map_sum, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        Algebra.TensorProduct.map_tmul] using hz
    exact Fintype.linearIndependent_iff.1 (Algebra.TensorProduct.basis A b).linearIndependent _ hz' i
  have hc : ∀ i, B.repr z i = 0 := fun i =>
    adele_eq_zero_of_comp (fun v => key (evFin F v) (hf v) i) (fun w => key (evInf F w) (hi w) i)
  rw [← B.sum_repr z]
  simp [hc]

variable {σ : E →ₐ[F] E} {n : ℕ} {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

end GlobalTheory.SWOpFin
