import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AdditiveValuationNorms.CokLenLeOfRangeLe

open UpperTheory.V UpperTheory.V.PropA

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Introduce a local definition for the expression. Establish an intermediate fact. Introduce a local definition for the expression.

Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the indicated hypotheses using the stated equalities. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result.

Supply the required witnesses or components. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem UpperTheory.V.PropA.cokL :
    ∀ (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (R : ℕ), GenBy l R X → cokLen ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X)) ≤ R := by
  intro l _ X _ _ R hgen
  obtain ⟨π, hπ⟩ := hgen
  classical
  let I : Submodule ℤ_[l] ℤ_[l] := IsLocalRing.maximalIdeal ℤ_[l]
  have hsimple : IsSimpleModule ℤ_[l] (ℤ_[l] ⧸ I) :=
    isSimpleModule_iff_isCoatom.2 (Ideal.isMaximal_def.1 (IsLocalRing.maximalIdeal.isMaximal ℤ_[l]))
  let P : Submodule ℤ_[l] (Fin R → ℤ_[l]) := Submodule.pi Set.univ (fun _ => I)
  let q : Submodule ℤ_[l] X := LinearMap.range ((l : ℤ_[l]) • (1 : Module.End ℤ_[l] X))
  have hle : P ≤ q.comap π := by
    intro v hv
    rw [Submodule.mem_pi] at hv
    have hex : ∀ i, ∃ w : ℤ_[l], v i = (l : ℤ_[l]) * w := by
      intro i
      have hi := hv i (Set.mem_univ i)
      change v i ∈ IsLocalRing.maximalIdeal ℤ_[l] at hi
      rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at hi
      obtain ⟨a, ha⟩ := hi
      exact ⟨a, by rw [← ha, mul_comm]⟩
    choose w hw using hex
    have hv' : v = (l : ℤ_[l]) • w := funext fun i => by simp [hw i]
    rw [Submodule.mem_comap, LinearMap.mem_range]
    refine ⟨π w, ?_⟩
    rw [LinearMap.smul_apply, Module.End.one_apply, hv', map_smul]
  have hφ : Function.Surjective (P.mapQ q π hle) := by
    intro z
    refine Submodule.Quotient.induction_on _ z ?_
    intro x
    obtain ⟨v, rfl⟩ := hπ x
    exact ⟨Submodule.Quotient.mk v, Submodule.mapQ_apply _ _ _ _⟩
  have h1 := Module.length_le_of_surjective (P.mapQ q π hle) hφ
  have h2 : Module.length ℤ_[l] ((Fin R → ℤ_[l]) ⧸ P) = R := by
    rw [(Submodule.quotientPi (fun _ : Fin R => I)).length_eq, Module.length_pi_of_fintype]
    simp [Module.length_eq_one]
  exact h1.trans h2.le
