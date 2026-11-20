import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleArith
import GroundTheory.HeightsAndTheta.Heights.Intersections.IsSmoothHermOfIsPullHermInl
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleMultiHomog
import GroundTheory.HeightsAndTheta.Heights.Intersections.StProjBundleDim
import GroundTheory.HeightsAndTheta.Heights.Intersections.PProjBundleFibre
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Lemmas

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem rename_inlV_mem_projBundleIdeal_iff (P : Ideal (MRing ι)) {N1 n : ℕ}
    (B : Matrix (Fin n) (Fin N1) (FnField P)) (f : MRing ι) :
    rename (inlV (ι₂ := fun _ : Unit => Fin N1)) f ∈ projBundleIdeal P B ↔ f ∈ P := by
  change f ∈ imageZ (inlV (ι₂ := fun _ : Unit => Fin N1)) (projBundleIdeal P B) ↔ f ∈ P
  rw [imageZ_projBundleIdeal]

end Lemmas

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Assume the hypotheses and unpack their components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. A detailed English derivation is pending.
-/
theorem ProjBundleArith.proof (hMH : ProjBundleMultiHomog.Statement) (hDim : ProjBundleDim.Statement) :
    ProjBundleArith.Statement := by
  intro K _ ι _ N1 t P d c m B hP hQ hB
  have hP' := hP
  obtain ⟨hK, ⟨_, _, hPr⟩, hPz, hPd⟩ := hP
  have hmem := rename_inlV_mem_projBundleIdeal_iff P B
  refine ⟨inferInstance, ⟨RingHom.ker_isPrime _, hMH K ι N1 t 2 P d c m B hP' hQ hB, ?_⟩, ?_, ?_⟩
  · rintro (k | u)
    · obtain ⟨i, hi⟩ := hPr k
      refine ⟨i, fun h => hi ((hmem _).1 ?_)⟩
      simpa [inlV] using h
    · obtain ⟨j, hj⟩ := Function.ne_iff.mp (hB.1.ne_zero 0)
      refine ⟨j, fun h => hj ?_⟩
      have h' : projBundleMap P B (X ⟨Sum.inr u, j⟩) = 0 := h
      rw [projBundleMap_X_inr] at h'
      have := congrArg (coeff (Finsupp.single 0 1)) h'
      simpa [coeff_X, Finsupp.single_eq_single_iff] using this
  · ext z
    rw [Ideal.mem_comap, Ideal.mem_bot]
    constructor
    · intro h
      have h2 : (C z : MRing ι) ∈ P := (hmem (C z)).1 (by simpa using h)
      have h3 : z ∈ P.comap (C : ℤ →+* MRing ι) := h2
      rw [hPz] at h3
      exact h3
    · rintro rfl
      simp
  · rw [hDim K ι N1 2 P d B hP' hB.1, hPd, ← Nat.cast_add]
    congr 1
    simp [Fintype.card_sum]
    omega

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
