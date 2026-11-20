import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

noncomputable section

namespace GlobalTheory.RealLift.Dbl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. By extensionality, compare the relevant components.

Apply the first step, then apply the next step to every resulting obligation. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem dblM_gram {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : Cᵀ * N * C.map star = Jm R S) :
    (dblM C)ᵀ * Matrix.fromBlocks N 0 0 (-N) * (dblM C).map star = Jm (R + S) (S + R) := by
  have hG : ∀ a a', ∑ x, (∑ y, C y a * N y x) * (starRingEnd ℂ) (C x a') = Jm R S a a' := by
    intro a a'
    have := congrFun (congrFun h a) a'
    simpa [Matrix.mul_apply] using this
  ext j k
  rcases j with p | p <;> rcases k with q | q <;>
  · obtain ⟨x, rfl⟩ := finSumFinEquiv.surjective p
    obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective q
    rcases x with r | s <;> rcases y with r' | s' <;>
      simp [Matrix.mul_apply, Fintype.sum_sum_type, dblM, dblCol, hG, Jm, Formalism.UG.Jpq, Matrix.one_apply,
        Finset.sum_neg_distrib, Matrix.neg_apply, Fin.ext_iff] <;> omega

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.
-/
theorem dblM_rinv {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (C : Matrix β (Ix R S) ℂ)
    (h : ∃ C' : Matrix (Ix R S) β ℂ, C * C' = 1) :
    ∃ D : Matrix (Ix (R + S) (S + R)) (β ⊕ β) ℂ, dblM C * D = 1 := by
  obtain ⟨C', hC'⟩ := h
  refine ⟨(dblM C'ᵀ)ᵀ, ?_⟩
  have hI : ∀ i i', ∑ r, C i (Sum.inl r) * C' (Sum.inl r) i' + ∑ s, C i (Sum.inr s) * C' (Sum.inr s) i' =
      (1 : Matrix β β ℂ) i i' := by
    intro i i'
    rw [← hC', Matrix.mul_apply, Fintype.sum_sum_type]
  ext i i'
  rcases i with i | i <;> rcases i' with i' | i' <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_add, dblM, dblCol, Matrix.one_apply, hI, add_comm]

/- English proof (translation)
Supply the required witnesses or components.
-/
theorem dblM_isFrame {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (N : Matrix β β ℂ) (C : Matrix β (Ix R S) ℂ)
    (h : IsFrame N C) : IsFrame (Matrix.fromBlocks N 0 0 (-N)) (dblM C) :=
  ⟨dblM_gram N C h.1, dblM_rinv C h.2⟩

/- English proof (translation)
Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem framed_dbl (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (α β : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] (P Q R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) :
    Framed τ JA JB a b A C → Framed τ JA (dbl JB) a b A (fun w => dblM (C w)) := by
  rintro ⟨hab, hA, hC⟩
  refine ⟨hab, hA, fun w => ?_⟩
  have key : b • (dbl JB).map (piInf (τ w)) =
      Matrix.fromBlocks (b • JB.map (piInf (τ w))) 0 0 (-(b • JB.map (piInf (τ w)))) := by
    simp [dbl, Matrix.fromBlocks_map, Matrix.fromBlocks_smul, Matrix.map_neg]
  rw [key]
  exact dblM_isFrame _ _ (hC w)

end GlobalTheory.RealLift.Dbl

end
