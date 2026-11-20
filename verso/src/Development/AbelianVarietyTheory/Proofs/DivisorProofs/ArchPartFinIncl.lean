import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombineApply

noncomputable section

namespace GlobalTheory.ArchFinSplit

open NumberField IsDedekindDomain GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def archPart (τ : ∀ w : InfinitePlace F, EmbOver E w) : AE F E →+* (InfinitePlace F → ℂ) :=
  RingHom.pi fun w => piInf (τ w)

variable (F E) in

def finPart : AE F E →+* E ⊗[F] FiniteAdeleRing (𝓞 F) F :=
  (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toRingHom.comp
    (Algebra.TensorProduct.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
      (AlgHom.id F E)).toRingHom

def splitHom (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    AE F E →+* (InfinitePlace F → ℂ) × (E ⊗[F] FiniteAdeleRing (𝓞 F) F) :=
  (archPart τ).prod (finPart F E)

variable (F E) in

def finIncl : E ⊗[F] FiniteAdeleRing (𝓞 F) F →ₗ[F] AE F E :=
  (LinearMap.rTensor E (LinearMap.inr F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).comp
    (TensorProduct.comm F E (FiniteAdeleRing (𝓞 F) F)).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finIncl_tmul (x : E) (a : FiniteAdeleRing (𝓞 F) F) :
    finIncl F E (x ⊗ₜ[F] a) = ((0, a) : AdeleRing (𝓞 F) F) ⊗ₜ[F] x := rfl

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem archPart_finIncl (τ : ∀ w : InfinitePlace F, EmbOver E w) (y : E ⊗[F] FiniteAdeleRing (𝓞 F) F) :
    archPart τ (finIncl F E y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]
  | tmul x a =>
    funext w
    show InfinitePlace.Completion.extensionEmbedding w (0 : w.Completion) * (τ w).1 x = 0
    rw [map_zero, zero_mul]

/- English proof (translation)
Proceed by induction. Treat this case separately. Treat this case separately. Treat this case separately.
-/
theorem finPart_finIncl (y : E ⊗[F] FiniteAdeleRing (𝓞 F) F) : finPart F E (finIncl F E y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul x a => rfl

end GlobalTheory.ArchFinSplit
