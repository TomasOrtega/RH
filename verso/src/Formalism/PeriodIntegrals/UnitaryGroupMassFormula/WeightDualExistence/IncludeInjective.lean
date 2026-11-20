import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualExistence.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.AlgWtDualEx

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => NumberField.maximalRealSubfield L

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem exists_place : Nonempty (IsDedekindDomain.HeightOneSpectrum (𝓞 L⁺)) := by
  obtain ⟨I, hbot, htop⟩ := Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp
    (NumberField.RingOfIntegers.not_isField L⁺)
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I htop.ne
  exact ⟨⟨M, hM.isPrime, fun h => by
    rw [h] at hIM
    exact hbot.ne' (le_bot_iff.mp hIM)⟩⟩

instance nontrivial_AFplus : Nontrivial (AFplus L) := by
  obtain ⟨v⟩ := exists_place L
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have := congrArg (evalAt L v) h
  rw [map_zero, map_one] at this
  exact zero_ne_one this

instance nontrivial_AL : Nontrivial (AL L) :=
  Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left _ _ _
    (algebraMap (L⁺) (AFplus L)).injective

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem include_injective :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) :=
  (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L).injective

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. By extensionality, compare the relevant components.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem unitaryOfMatch : UnitaryOfMatch L n := by
  intro γ γ₀ hm
  have hγ : ((γ : GAf L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map (Matrix.GeneralLinearGroup.map
      (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L)) := γ.2
  obtain ⟨γ₁, h₁, he⟩ := hγ
  have hmat : (γ₀ : Matrix (Fin n) (Fin n) L) = (γ₁ : Matrix (Fin n) (Fin n) L) := by
    ext i j
    apply include_injective L
    have e1 := congrFun (congrFun hm i) j
    have e2 := congrArg (fun g : GL (Fin n) (AL L) => (g : Matrix (Fin n) (Fin n) (AL L)) i j) he
    simp only [Matrix.map_apply] at e1 e2
    rw [← e1]
    rw [← e2]
    rfl
  have : γ₀ = γ₁ := Units.ext hmat
  rw [this]
  exact h₁

end PI.UnitaryGroupMassFormula.AlgWtDualEx
