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

namespace GlobalTheory

/- English proof (translation)
Establish `hd : IsUnit Q.det` using `(Matrix.isUnit_iff_isUnit_det Q).mp hQ`. Establish `hl : Q⁻¹ * Q = 1` using `Matrix.nonsing_inv_mul Q hd`. Establish `key : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) = Q⁻¹ * (∑ a, ∑ b, (Q * Y * Q⁻¹) a b • Matrix.single a b (1 : ℂ)) * Q`. Simplify using `only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]`. Establish `hM : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • Matrix.single a b (1 : ℂ) = Q * Y * Q⁻¹` using `by conv_rhs => rw [Matrix.matrix_eq_sum_single (Q * Y * Q⁻¹)]`.

Simplify using `only [Matrix.smul_single, smul_eq_mul, mul_one]`. Rewrite using `[key, hM]`. Simplify using `only [Matrix.mul_assoc, hl, Matrix.mul_one]`. Rewrite using `[← Matrix.mul_assoc, hl, Matrix.one_mul]`.
-/
theorem conj_expand_units {n : ℕ} (Q Y : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) :
    Y = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hl : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hd
  have key : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q)
      = Q⁻¹ * (∑ a, ∑ b, (Q * Y * Q⁻¹) a b • Matrix.single a b (1 : ℂ)) * Q := by
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  have hM : ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • Matrix.single a b (1 : ℂ) = Q * Y * Q⁻¹ := by
    conv_rhs => rw [Matrix.matrix_eq_sum_single (Q * Y * Q⁻¹)]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [key, hM]
  simp only [Matrix.mul_assoc, hl, Matrix.mul_one]
  rw [← Matrix.mul_assoc, hl, Matrix.one_mul]

/- English proof (translation)
Establish `hd : IsUnit Q.det` using `(Matrix.isUnit_iff_isUnit_det Q).mp hQ`. Establish `hr : Q * Q⁻¹ = 1` using `Matrix.mul_nonsing_inv Q hd`. Establish `e1 : (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) = Q⁻¹ * (Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ)) * Q`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc]`.

Use `_ = Q⁻¹ * (Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ)) * Q := by`. Rewrite using `[hr, Matrix.one_mul]`. Rewrite using `[e1]`. Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality.

Simplify using `[Matrix.single_mul_single_same]`. Rewrite using `[Matrix.single_mul_single_of_ne (1 : ℂ) a b c hbc (1 : ℂ)]`. Simplify using `[hbc]`.
-/
theorem conj_units_mul {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (hQ : IsUnit Q) (a b c d : Fin n) :
    (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = (if b = c then (1 : ℂ) else 0) • (Q⁻¹ * Matrix.single a d (1 : ℂ) * Q) := by
  have hd : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).mp hQ
  have hr : Q * Q⁻¹ = 1 := Matrix.mul_nonsing_inv Q hd
  have e1 : (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
      = Q⁻¹ * (Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ)) * Q := by
    calc (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) * (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q)
        = Q⁻¹ * (Matrix.single a b (1 : ℂ) * ((Q * Q⁻¹) * Matrix.single c d (1 : ℂ))) * Q := by
          simp only [Matrix.mul_assoc]
      _ = Q⁻¹ * (Matrix.single a b (1 : ℂ) * Matrix.single c d (1 : ℂ)) * Q := by
          rw [hr, Matrix.one_mul]
  rw [e1]
  by_cases hbc : b = c
  · subst hbc
    simp [Matrix.single_mul_single_same]
  · rw [Matrix.single_mul_single_of_ne (1 : ℂ) a b c hbc (1 : ℂ)]
    simp [hbc]

/- English proof (translation)
Introduce `hK k r ε mu R hDG Q E hQ hE`. Take `⟨-, -, hlinY, hLie, hbr, -⟩` from `Gp91.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hDG`. Establish `hv0 : ∀ v : R.smSub, (v : R.H) ∈ R.sm` using `fun v => v.2`. Establish `hE' : ∀ (a b : Fin (2 * r + k + 1)) (v : R.smSub), ((E a b v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) v` using `hE`. Establish `h0 : ∀ v : R.smSub, R.dC 0 (v : R.H) = 0` using `fun v => by`.

Use `hlinY 0 0 1 v (hv0 v)` as an intermediate fact. Simplify using `using this`. Set `f : R.smSub → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℂ] R.H` to `fun v => { toFun := fun Y => R.dC Y v map_add' := fun Y Z => by`. Use `hlinY Y Z 1 v (hv0 v)` as an intermediate fact. Simplify using `using this`.

Use the proof step `map_smul' := fun a Y => by`. Use `hlinY Y 0 a v (hv0 v)` as an intermediate fact. Simplify `this }` using `[h0 v]`. Establish `hsub : ∀ (Y Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : R.smSub), R.dC (Y - Z) (v : R.H) = R.dC Y v - R.dC Z v` using `fun Y Z v => map_sub (f v) Y Z`. Establish `hsm : ∀ (a : ℂ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : R.smSub), R.dC (a • Y) (v : R.H) = a • R.dC Y v` using `fun a Y v => map_smul (f v) a Y`.

Establish `hexpP : ∀ (P Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsUnit P → (∀ (a b : Fin (2 * r + k + 1)) (v : R.smSub), ((E a b v : R.smSub) : R.H) = R.dC (P⁻¹ * Matrix.single a b (1 : ℂ) * P) v) → ∀ v : R.smSub, R.dC Y v = ∑ a, ∑ b, (P * Y * P⁻¹) a b • ((E a b v : R.smS …`. Introduce `P Y hP hPE v`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_sum, map_smul]`. Use `_ = ∑ a, ∑ b, (P * Y * P⁻¹) a b • ((E a b v : R.smSub) : R.H) := by`.

Simplify using `only [hPE]`. Both sides reduce to the same expression. Establish `hexp : ∀ (Y : Mx k r) (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)` using `fun Y v => hexpP Q Y hQ hE v`. Establish `hGl : Formalism.REAL.GlRel E`. Introduce `a b c d`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `hb` using `hbr (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v (hv0 v)`. Rewrite `hb` using `[conj_units_mul Q hQ, conj_units_mul Q hQ]`.

Establish `lhs : (((E a b * E c d - E c d * E a b) v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (R.dC (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v) - R.dC (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) (R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) v)`. Simplify using `[hE']`. Rewrite using `[lhs, hb, hsub, hsm, hsm]`. Apply the tactic sequence `by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, hE']`. Use `⟨hGl, hexp, fun X hX v => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hLie X hX v (hv0 v)]`. Conclude with `hexp X v`.
-/
theorem dC_expand_units : PI.KFinSmooth → ∀ (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (R : Rep k r), R.IsDG ε mu → ∀ (Q : Mx k r) (E : (Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ R.smSub)), IsUnit Q → R.IsE Q E → Formalism.REAL.GlRel E ∧ (∀ Y (v : R.smSub), R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H)) ∧ ∀ X, PI.UpqRep.InLieHpk k r X → ∀ v : R.smSub, PI.UpqRep.dsig (k := k) (r := r) R.σ X v = ∑ a, ∑ b, (Q * X * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
  intro hK k r ε mu R hDG Q E hQ hE
  obtain ⟨-, -, hlinY, hLie, hbr, -⟩ := Gp91.GlobalTheory.T.complexifiedDerivedAction_lieHom_gramAdjoint hK k r ε mu R hDG
  have hv0 : ∀ v : R.smSub, (v : R.H) ∈ R.sm := fun v => v.2
  have hE' : ∀ (a b : Fin (2 * r + k + 1)) (v : R.smSub),
      ((E a b v : R.smSub) : R.H) = R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) v := hE
  have h0 : ∀ v : R.smSub, R.dC 0 (v : R.H) = 0 := fun v => by
    have := hlinY 0 0 1 v (hv0 v)
    simpa using this
  let f : R.smSub → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ →ₗ[ℂ] R.H := fun v =>
    { toFun := fun Y => R.dC Y v
      map_add' := fun Y Z => by
        have := hlinY Y Z 1 v (hv0 v)
        simpa using this
      map_smul' := fun a Y => by
        have := hlinY Y 0 a v (hv0 v)
        simpa [h0 v] using this }
  have hsub : ∀ (Y Z : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : R.smSub),
      R.dC (Y - Z) (v : R.H) = R.dC Y v - R.dC Z v := fun Y Z v => map_sub (f v) Y Z
  have hsm : ∀ (a : ℂ) (Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : R.smSub),
      R.dC (a • Y) (v : R.H) = a • R.dC Y v := fun a Y v => map_smul (f v) a Y
  have hexpP : ∀ (P Y : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), IsUnit P →
      (∀ (a b : Fin (2 * r + k + 1)) (v : R.smSub),
        ((E a b v : R.smSub) : R.H) = R.dC (P⁻¹ * Matrix.single a b (1 : ℂ) * P) v) →
      ∀ v : R.smSub, R.dC Y v = ∑ a, ∑ b, (P * Y * P⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
    intro P Y hP hPE v
    calc R.dC Y v = f v Y := rfl
      _ = f v (∑ a, ∑ b, (P * Y * P⁻¹) a b • (P⁻¹ * Matrix.single a b (1 : ℂ) * P)) :=
          congrArg (f v) (conj_expand_units P Y hP)
      _ = ∑ a, ∑ b, (P * Y * P⁻¹) a b • f v (P⁻¹ * Matrix.single a b (1 : ℂ) * P) := by
          simp only [map_sum, map_smul]
      _ = ∑ a, ∑ b, (P * Y * P⁻¹) a b • ((E a b v : R.smSub) : R.H) := by
          simp only [hPE]
          rfl
  have hexp : ∀ (Y : Mx k r) (v : R.smSub),
      R.dC Y v = ∑ a, ∑ b, (Q * Y * Q⁻¹) a b • ((E a b v : R.smSub) : R.H) :=
    fun Y v => hexpP Q Y hQ hE v
  have hGl : Formalism.REAL.GlRel E := by
    intro a b c d
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    have hb := hbr (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v (hv0 v)
    rw [conj_units_mul Q hQ, conj_units_mul Q hQ] at hb
    have lhs : (((E a b * E c d - E c d * E a b) v : R.smSub) : R.H) =
        R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) (R.dC (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) v)
        - R.dC (Q⁻¹ * Matrix.single c d (1 : ℂ) * Q) (R.dC (Q⁻¹ * Matrix.single a b (1 : ℂ) * Q) v) := by
      simp [hE']
    rw [lhs, hb, hsub, hsm, hsm]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, hE']
  refine ⟨hGl, hexp, fun X hX v => ?_⟩
  rw [← hLie X hX v (hv0 v)]
  exact hexp X v

end GlobalTheory
