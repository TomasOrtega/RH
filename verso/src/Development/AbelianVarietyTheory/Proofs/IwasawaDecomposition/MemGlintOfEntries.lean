import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DatVtEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StdMaximalCompactReductionPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSpherical

namespace GlobalTheory.MemGlintOfEntries

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression.

Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

By extensionality, compare the relevant components. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem mem_glint_of_entries {K : Type} [inst : Field K] {n : ℕ} (O : Subring K)
    (g : GL (Fin n) K)
    (h : ∀ (i j : Fin n), (↑g : Matrix (Fin n) (Fin n) K) i j ∈ O)
    (h' : ∀ (i j : Fin n), (↑g⁻¹ : Matrix (Fin n) (Fin n) K) i j ∈ O) :
    g ∈ Formalism.UG.GLint (Fin n) O := by
  let A : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h i j⟩
  let B : Matrix (Fin n) (Fin n) O := Matrix.of fun i j => ⟨_, h' i j⟩
  have hA : O.subtype.mapMatrix A = (↑g : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hB : O.subtype.mapMatrix B = (↑g⁻¹ : Matrix (Fin n) (Fin n) K) := by
    ext i j; rfl
  have hinj : Function.Injective
      (O.subtype.mapMatrix : Matrix (Fin n) (Fin n) O → Matrix (Fin n) (Fin n) K) := by
    intro X Y hXY
    ext i j
    exact congrFun (congrFun hXY i) j
  have hAB : A * B = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.mul_inv g
  have hBA : B * A = 1 := by
    apply hinj
    rw [map_mul, map_one, hA, hB]
    exact Units.inv_mul g
  refine ⟨⟨A, B, hAB, hBA⟩, ?_⟩
  apply Units.ext
  ext i j
  rfl

end GlobalTheory.MemGlintOfEntries
