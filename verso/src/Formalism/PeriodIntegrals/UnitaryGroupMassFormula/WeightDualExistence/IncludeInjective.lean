import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeightDualExistence.Development

noncomputable section

namespace PI.UnitaryGroupMassFormula.AlgWtDualEx

open NumberField Formalism.L2.NG ReciprocityTheory.Aut Formalism.AUTREP

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

local notation3 "L⁺" => NumberField.maximalRealSubfield L

/- English proof (translation)
Take `⟨I, hbot, htop⟩` from `Ring.not_isField_iff_exists_ideal_bot_lt_and_lt_top.mp (NumberField.RingOfIntegers.not_isField L⁺)`. Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I htop.ne`. Conclude with `⟨⟨M, hM.isPrime, fun h => by`. Rewrite `hIM` using `[h]`. Conclude with `hbot.ne' (le_bot_iff.mp hIM)⟩⟩`.
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
The claim follows from `(Algebra.TensorProduct.includeLeftRingHom : L →+* AL L).injective`.
-/
theorem include_injective :
    Function.Injective (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L) :=
  (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L).injective

/- English proof (translation)
Introduce `γ γ₀ hm`. Establish `hγ : ((γ : GAf L n) : GL (Fin n) (AL L)) ∈ (GQ0 L n).map (Matrix.GeneralLinearGroup.map (Algebra.TensorProduct.includeLeftRingHom : L →+* AL L))` using `γ.2`. Take `⟨γ₁, h₁, he⟩` from `hγ`. Establish `hmat : (γ₀ : Matrix (Fin n) (Fin n) L) = (γ₁ : Matrix (Fin n) (Fin n) L)`. Use extensionality with `i j`.

Apply `include_injective L` to reduce the goal to its premises. Establish `e1` using `congrFun (congrFun hm i) j`. Establish `e2` using `congrArg (fun g : GL (Fin n) (AL L) => (g : Matrix (Fin n) (Fin n) (AL L)) i j) he`. Simplify using `only [Matrix.map_apply] at e1 e2`. Rewrite using `[← e1]`.

Rewrite using `[← e2]`. Both sides reduce to the same expression. Establish `: γ₀ = γ₁` using `Units.ext hmat`. Rewrite using `[this]`. Conclude with `h₁`.
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
