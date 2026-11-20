import Mathlib
import CompanionTheory.AutomorphicTheory.PieriRules.PieriDegreeBounds.Imports
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementKT
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.ComplexifiedDerivedActionLieHomGramAdjointStatement
import CompanionTheory.AutomorphicTheory.PieriRules.ThetaBesselIsometries.IsDSOfIsDG

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapUnitary

/- English proof (translation)
Use extensionality with `i j`. Unfold `PI.UpqRep.Jm Formalism.REAL.sgn`. Rewrite using `[Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]`. Distinguish the cases in `h : b = i ∧ a = j`. Take `⟨rfl, rfl⟩` from `h`.

Apply the tactic sequence `cases ε a <;> cases ε b <;> simp`. Simplify using `[h]`.
-/
theorem diag_single {n : ℕ} (ε : Fin n → Bool) (a b : Fin n) :
    PI.UpqRep.Jm ε * Matrix.single b a (1 : ℂ) * PI.UpqRep.Jm ε
      = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • Matrix.single b a (1 : ℂ) := by
  ext i j
  unfold PI.UpqRep.Jm Formalism.REAL.sgn
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.smul_apply, Matrix.single_apply]
  by_cases h : b = i ∧ a = j
  · obtain ⟨rfl, rfl⟩ := h
    cases ε a <;> cases ε b <;> simp
  · simp [h]

/- English proof (translation)
Establish `h1 : Q * Qᴴ = 1` using `Matrix.mem_unitaryGroup_iff.mp hQ`. Establish `hi : Q⁻¹ = Qᴴ` using `Matrix.inv_eq_right_inv h1`. Establish `h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Q * (Qᴴ * M) = M` using `fun M => by`. Rewrite using `[← Matrix.mul_assoc, h1, Matrix.one_mul]`. Rewrite using `[hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_single, star_one, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diag_single]`.

Simplify using `only [Matrix.mul_assoc, h2]`.
-/
theorem adj_unit {n : ℕ} (ε : Fin n → Bool) (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (a b : Fin n) :
    (Qᴴ * PI.UpqRep.Jm ε * Q) * (Q⁻¹ * Matrix.single a b 1 * Q)ᴴ * (Qᴴ * PI.UpqRep.Jm ε * Q)
      = ((Formalism.REAL.sgn ε a b : ℝ) : ℂ) • (Q⁻¹ * Matrix.single b a 1 * Q) := by
  have h1 : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hQ
  have hi : Q⁻¹ = Qᴴ := Matrix.inv_eq_right_inv h1
  have h2 : ∀ M : Matrix (Fin n) (Fin n) ℂ, Q * (Qᴴ * M) = M := fun M => by
    rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [hi, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_single, star_one, ← Matrix.smul_mul, ← Matrix.mul_smul, ← diag_single]
  simp only [Matrix.mul_assoc, h2]

/- English proof (translation)
Introduce `hK k r ε mu R hR Q E hQ hE a b x y`. Take `⟨-, -, hlin, -, -, hadj⟩` from `GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR`. Establish `hH : Formalism.QuantumDeterminants.Hpk k r = Qᴴ * PI.UpqRep.Jm ε * Q` using `hQ.1.2.symm`. Establish `h0 : R.dC 0 (y : R.H) = 0`. Use `hlin 0 0 1 y y.2` as an intermediate fact.

Simplify using `using this`. Establish `hs : ∀ (c : ℂ) Y, R.dC (c • Y) (y : R.H) = c • R.dC Y (y : R.H)` using `fun c Y => by`. Use `hlin Y 0 c y y.2` as an intermediate fact. Rewrite `this` using `[add_zero, h0, add_zero]`. Then use the resulting hypothesis. Rewrite using `[Submodule.coe_inner, Submodule.coe_inner, hE, hE, hadj _ _ x.2 _ y.2, hH, adj_unit ε Q hQ.2, hs, inner_smul_right]`.
-/
theorem isUnitary_of_isE : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), PI.UpqRep.IsCayleyU k r ε Q → R.IsE Q E → Formalism.REAL.IsUnitary ε E := by
  intro hK k r ε mu R hR Q E hQ hE a b x y
  obtain ⟨-, -, hlin, -, -, hadj⟩ := GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hR
  have hH : Formalism.QuantumDeterminants.Hpk k r = Qᴴ * PI.UpqRep.Jm ε * Q := hQ.1.2.symm
  have h0 : R.dC 0 (y : R.H) = 0 := by
    have := hlin 0 0 1 y y.2
    simpa using this
  have hs : ∀ (c : ℂ) Y, R.dC (c • Y) (y : R.H) = c • R.dC Y (y : R.H) := fun c Y => by
    have := hlin Y 0 c y y.2
    rwa [add_zero, h0, add_zero] at this
  rw [Submodule.coe_inner, Submodule.coe_inner, hE, hE, hadj _ _ x.2 _ y.2, hH, adj_unit ε Q hQ.2, hs,
    inner_smul_right]

end GlobalTheory.CapUnitary
