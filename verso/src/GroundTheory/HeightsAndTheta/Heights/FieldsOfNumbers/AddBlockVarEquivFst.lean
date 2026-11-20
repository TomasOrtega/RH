import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PfContractedHypothesesExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

namespace AddBlockFunctionField

section Projection

variable {F : Type u} [Field F] {K L : Type} {ι : K → Type} {ι₂ : L → Type}

/- English proof (translation)
Both sides reduce to the same expression.
-/
example : MRing (fun k => Sum.elim ι ι₂ ((Function.Embedding.inl : K ↪ K ⊕ L) k)) F =
    MRing ι F := rfl

/- English proof (translation)
Use function extensionality and compare the values at `x`. Consider the cases of `x with`. Consider the case `inl k`. Conclude with `(Sum.inl_injective.extend_apply b 0 k)`. Consider the case `inr l`.

Use `Function.extend_apply' _ _ _ ?_` and prove the remaining obligations. Introduce and unpack `⟨k, hk⟩`. Conclude with `Sum.inl_ne_inr hk`.
-/
theorem pullDeg_inl (b : K → ℤ) :
    pullDeg (Function.Embedding.inl : K ↪ K ⊕ L) b = IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := L) b := by
  funext x
  cases x with
  | inl k =>
    exact (Sum.inl_injective.extend_apply b 0 k)
  | inr l =>
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨k, hk⟩
    exact Sum.inl_ne_inr hk

/- English proof (translation)
Unfold `IndefiniteRowSideFullHecke.FieldNumbers.pulledFunField homFracDegZero`. Rewrite using `[IntermediateField.adjoin_map]`. Use `congr 1`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨d, f, g, hf, hg, hgP, rfl⟩`. Use `⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `[contractFracMap, contractQuot, map_div₀, IndefiniteRowSideFullHecke.FieldNumbers.blockIncl]`. Both sides reduce to the same expression. Introduce and unpack `⟨y, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩`.

Use `⟨d, f, g, hf, hg, hgP, ?_⟩` and prove the remaining obligations. Simplify using `[contractFracMap, contractQuot, map_div₀, IndefiniteRowSideFullHecke.FieldNumbers.blockIncl]`. Both sides reduce to the same expression.
-/
theorem pulledFunField_eq [DecidableEq K] (P' : Ideal (MRing (Sum.elim ι ι₂) F)) [P'.IsPrime] :
    IndefiniteRowSideFullHecke.FieldNumbers.pulledFunField ι₂ P' =
      (homFracDegZero (contractPrime (Function.Embedding.inl : K ↪ K ⊕ L) P')).map
        (contractFracMap Function.Embedding.inl P') := by
  unfold IndefiniteRowSideFullHecke.FieldNumbers.pulledFunField homFracDegZero
  rw [IntermediateField.adjoin_map]
  congr 1
  ext x
  constructor
  · rintro ⟨d, f, g, hf, hg, hgP, rfl⟩
    refine ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, ?_⟩
    simp [contractFracMap, contractQuot, map_div₀, IndefiniteRowSideFullHecke.FieldNumbers.blockIncl]
    rfl
  · rintro ⟨y, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    refine ⟨d, f, g, hf, hg, hgP, ?_⟩
    simp [contractFracMap, contractQuot, map_div₀, IndefiniteRowSideFullHecke.FieldNumbers.blockIncl]
    rfl

/- English proof (translation)
Unfold `relDeg IndefiniteRowSideFullHecke.FieldNumbers.fibreDeg`. Rewrite using `[pulledFunField_eq]`. Both sides reduce to the same expression.
-/
theorem relDeg_inl [DecidableEq K] [DecidableEq L] (P' : Ideal (MRing (Sum.elim ι ι₂) F))
    [P'.IsPrime] :
    relDeg (Function.Embedding.inl : K ↪ K ⊕ L) P' = IndefiniteRowSideFullHecke.FieldNumbers.fibreDeg ι₂ P' := by
  unfold relDeg IndefiniteRowSideFullHecke.FieldNumbers.fibreDeg
  rw [pulledFunField_eq]
  rfl

end Projection

section NewBlock

variable {F : Type u} [Field F] {K : Type} {ι : K → Type}

abbrev blockEquiv (K : Type) : Option K ≃ K ⊕ Unit := Equiv.optionEquivSumPUnit K

def addBlockVarEquiv (ι : K → Type) (N : ℕ) :
    (Σ o, addBlock ι N o) ≃ (Σ s, Sum.elim ι (fun _ : Unit => Fin (N + 1)) s) where
  toFun v := match v with
    | ⟨none, i⟩ => ⟨Sum.inr (), i⟩
    | ⟨some k, x⟩ => ⟨Sum.inl k, x⟩
  invFun v := match v with
    | ⟨Sum.inl k, x⟩ => ⟨some k, x⟩
    | ⟨Sum.inr (), i⟩ => ⟨none, i⟩
  left_inv v := by rcases v with ⟨_ | k, x⟩ <;> rfl
  right_inv v := by rcases v with ⟨k | ⟨⟩, x⟩ <;> rfl

def addBlockRingEquiv (ι : K → Type) (N : ℕ) :
    MRing (addBlock ι N) F ≃ₐ[F] MRing (Sum.elim ι (fun _ : Unit => Fin (N + 1))) F :=
  renameEquiv F (addBlockVarEquiv ι N)

/- English proof (translation)
Use function extensionality and compare the values at `o`. Consider the cases of `o with`. Consider the case `some k => exact (Option.some_injective K).extend_apply c 0 k`. Consider the case `none`. Use `Function.extend_apply' _ _ _ ?_` and prove the remaining obligations.

Introduce and unpack `⟨k, hk⟩`. Conclude with `Option.some_ne_none k hk`.
-/
theorem pullDeg_some (c : K → ℤ) :
    pullDeg (Function.Embedding.some : K ↪ Option K) c =
      IndefiniteRowSideFullHecke.FieldNumbers.pullDeg (L := Unit) c ∘ blockEquiv K := by
  funext o
  cases o with
  | some k => exact (Option.some_injective K).extend_apply c 0 k
  | none =>
    refine Function.extend_apply' _ _ _ ?_
    rintro ⟨k, hk⟩
    exact Option.some_ne_none k hk

end NewBlock

end AddBlockFunctionField

end

end GroundTheory.Heights₂.Heights.FieldNumbers
