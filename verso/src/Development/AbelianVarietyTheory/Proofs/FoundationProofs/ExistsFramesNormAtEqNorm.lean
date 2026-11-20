import Mathlib
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataRRMetric
import Formalism.LocalToGlobal.LatticeGeometry.DegFlLApply
import Formalism.LocalToGlobal.LatticeGeometry.CmTypeMeetsConjugatePair
open Formalism.BasicNotions NumberField

namespace GlobalTheory

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Introduce a local definition for the expression. Establish an intermediate fact.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Separate the alternatives or extract the components of the hypothesis. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments.

Reduce the conclusion to the remaining proof obligations. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem exists_frames_normAt_eq_norm : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (e : K →+* ℂ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (n : ℕ) (c : Module.Basis (Fin n) ℂ W) (L : Submodule (𝓞 K) (Fin n → K)), ∃ X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ, (∀ v, IsUnit (X v).det) ∧ ∀ x : Fin n → K, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin n)) X (InfinitePlace.mk e) x = ‖∑ i, e (x i) • c i‖ := by
  intro K _ _ _ e W _ _ n c _
  have : FiniteDimensional ℂ W := Module.Finite.of_basis c
  have hn : Module.finrank ℂ W = n := by simpa using Module.finrank_eq_card_basis c
  let o : OrthonormalBasis (Fin n) ℂ W := (stdOrthonormalBasis ℂ W).reindex (finCongr hn)
  set A : Matrix (Fin n) (Fin n) ℂ := o.toBasis.toMatrix c with hA
  have hAu : IsUnit A.det :=
    Matrix.isUnit_det_of_right_inverse (o.toBasis.toMatrix_mul_toMatrix_flip c)
  have key : ∀ y : Fin n → ℂ, Formalism.HermitianLatticesTheory.cnorm (A.mulVec y) = ‖∑ i, y i • c i‖ := by
    intro y
    rw [← o.repr.norm_map, EuclideanSpace.norm_eq]
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 2
    simp [hA, Matrix.mulVec, dotProduct, Module.Basis.toMatrix_apply, mul_comm]
  rcases InfinitePlace.embedding_mk_eq e with h | h
  · refine ⟨fun _ => A⁻¹, fun _ => Matrix.isUnit_nonsing_inv_det A hAu, fun x => ?_⟩
    rw [← key]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.nonsing_inv_nonsing_inv A hAu]
    congr 2
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt, h]
  · have hBu : IsUnit (A.map (starRingEnd ℂ)).det := by
      have := hAu.map (starRingEnd ℂ)
      rwa [RingHom.map_det] at this
    refine ⟨fun _ => (A.map (starRingEnd ℂ))⁻¹, fun _ => Matrix.isUnit_nonsing_inv_det _ hBu,
      fun x => ?_⟩
    rw [← key]
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.nonsing_inv_nonsing_inv _ hBu]
    unfold Formalism.HermitianLatticesTheory.cnorm
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [← RCLike.norm_conj (A.mulVec (fun i => e (x i)) j)]
    congr 1
    simp [Formalism.HermitianLatticesTheory.vecAt, h, Matrix.mulVec, dotProduct]

end GlobalTheory
