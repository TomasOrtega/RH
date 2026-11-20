import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Establish an intermediate fact. Replace the relevant objects with their definitions.

Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. By extensionality, compare the relevant components. Establish an intermediate fact.

Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. A detailed English derivation is pending.
-/
theorem smallRank : SmallRank := by
  intro L _ _ ϖ σ q n hU hn g

  set A : Matrix (Fin n) (Fin n) L := ((g : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) with hAdef
  set B : Matrix (Fin n) (Fin n) L := (((g : GL (Fin n) L)⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
    with hBdef
  have hAB : A * B = 1 := (g : GL (Fin n) L).mul_inv
  have hBA : B * A = 1 := (g : GL (Fin n) L).inv_mul

  have hherm : (A.map σ)ᵀ * antiJ L n * A = antiJ L n := g.2

  have key : ∀ i j, Valued.v (A i j) = 1 ∧ Valued.v (B i j) = 1 := by
    intro i j
    obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
    · exact i.elim0
    · obtain rfl : i = 0 := Subsingleton.elim _ _
      obtain rfl : j = 0 := Subsingleton.elim _ _
      have h1 : σ (A 0 0) * A 0 0 = 1 := by
        simpa [Matrix.mul_apply, antiJ] using congrFun (congrFun hherm 0) 0
      have h2 : B 0 0 * A 0 0 = 1 := by
        simpa [Matrix.mul_apply] using congrFun (congrFun hBA 0) 0
      have hsq : Valued.v (A 0 0) * Valued.v (A 0 0) = 1 := by
        have := congrArg Valued.v h1
        rwa [map_mul, map_one, hU.2.1] at this
      have hle : Valued.v (A 0 0) ≤ 1 := by
        by_contra hlt
        have hgt : 1 < Valued.v (A 0 0) := not_le.1 hlt
        have : Valued.v (A 0 0) * 1 ≤ Valued.v (A 0 0) * Valued.v (A 0 0) := by gcongr
        rw [mul_one, hsq] at this
        exact hlt this
      have hA1 : Valued.v (A 0 0) = 1 := by
        refine le_antisymm hle ?_
        have : Valued.v (A 0 0) * Valued.v (A 0 0) ≤ Valued.v (A 0 0) * 1 := by gcongr
        rwa [mul_one, hsq] at this
      refine ⟨hA1, ?_⟩
      have := congrArg Valued.v h2
      rwa [map_mul, map_one, hA1, mul_one] at this
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => by
    unfold intL
    exact (Valuation.mem_integer_iff _ _).2 hx.le

  let A' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨A i j, hint _ (key i j).1⟩
  let B' : Matrix (Fin n) (Fin n) (intL L) := fun i j => ⟨B i j, hint _ (key i j).2⟩
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin n) (Fin n) (intL L) → Matrix (Fin n) (Fin n) L) :=
    fun X Y h => by
      ext i j
      exact congrFun (congrFun h i) j
  have eA : (intL L).subtype.mapMatrix A' = A := rfl
  have eB : (intL L).subtype.mapMatrix B' = B := rfl
  unfold KU
  rw [Subgroup.mem_subgroupOf]
  unfold intPts
  rw [Subgroup.mem_inf, MonoidHom.mem_range]
  refine ⟨g.2, ⟨A', B', hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, eA, eB, map_one, hAB]
  · rw [map_mul, eA, eB, map_one, hBA]
  · unfold bc
    exact Units.ext eA

end GlobalTheory.InertZeta

end
