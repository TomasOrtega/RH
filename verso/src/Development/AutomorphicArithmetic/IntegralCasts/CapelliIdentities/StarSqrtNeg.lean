import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataHost

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hre` using `congrArg Complex.re h`. Establish `him` using `congrArg Complex.im h`. Simplify using `[pow_two] at hre him`. Establish `hn' : (0 : ℝ) < n` using `by exact_mod_cast hn`. Establish `hz : z.re = 0`.

Establish `h2 : z.re * z.im = 0` using `by linarith`. Break down `mul_eq_zero.mp h2 with h1 | h1` into its components or cases. Conclude with `h1`. It suffices to derive a contradiction. Rewrite `hre` using `[h1]`.

Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Apply the tactic sequence `apply Complex.ext <;> simp [hz]`.
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
Introduce `D x n hn h`. Use `haveI : NumberField.IsCMField D.host.E := D.host.isCMField_hostE`. Take `⟨φ⟩ : Nonempty (D.host.E →+* ℂ)` from `inferInstance`. Apply `φ.injective` to reduce the goal to its premises. Establish `key : φ (Star.star x) = (starRingEnd ℂ) (φ x)` using `NumberField.IsCMField.complexEmbedding_complexConj D.host.E φ x`.

Establish `hsq : (φ x) ^ 2 = -(n : ℂ)`. Use `congrArg φ h` as an intermediate fact. Simplify using `using this`. Rewrite using `[key, map_neg]`. Conclude with `conj_eq_neg_of_sq hn hsq`.
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
