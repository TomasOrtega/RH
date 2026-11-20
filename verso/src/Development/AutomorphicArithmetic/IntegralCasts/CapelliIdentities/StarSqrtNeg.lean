import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis. It suffices to derive a contradiction. Rewrite the indicated hypotheses using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

Apply the first step, then apply the next step to every resulting obligation. A detailed English derivation is pending.
-/
private lemma conj_eq_neg_of_sq {z : ℂ} {n : ℕ} (hn : 0 < n) (h : z ^ 2 = -(n : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hz : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h1 | h1
    · exact h1
    · exfalso; rw [h1] at hre; nlinarith [mul_self_nonneg z.re]
  apply Complex.ext <;> simp [hz]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Reformulated.B.StarSqrtNeg.star_sqrt_neg :
    ∀ {D : Formalism.L2.Ker.Car} (x : D.host.E) (n : ℕ),
    (0 : ℕ) < n →
      x ^ (2 : ℕ) = -(↑n : D.host.E) →
        Star.star x =
          -x := by
  intro D x n hn h
  haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨φ⟩ : Nonempty (D.host.E →+* ℂ) := inferInstance
  apply φ.injective
  have key : φ (Star.star x) = (starRingEnd ℂ) (φ x) :=
    NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x
  have hsq : (φ x) ^ 2 = -(n : ℂ) := by
    have := congrArg φ h
    simpa using this
  rw [key, map_neg]
  exact conj_eq_neg_of_sq hn hsq
