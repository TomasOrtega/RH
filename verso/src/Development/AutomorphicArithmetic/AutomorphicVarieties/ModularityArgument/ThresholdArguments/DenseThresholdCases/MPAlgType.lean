import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.FiniteOrderCongruences.PAlgType
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutomorphicFormHyp

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N IsLocalRing Polynomial
open UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Ws UpperTheory.V.Sd UpperTheory.V.Sd.S3
open UpperTheory.V.Cu
open scoped Matrix
namespace UpperTheory.V.Cu2
namespace AlgType
variable {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {l : ℕ} [Fact l.Prime]
end AlgType
open AlgType in
/- English proof (translation)
Introduce `K Ω _ _ _ _ _ l _ ι art Y a κ ha h1 h2 n j`. Establish `H : Good art ι a κ` using `⟨Y, h1, h2⟩`. Establish `H1 : Good art ι (fun _ => 1) (cycBar K Ω l)` using `good_cyc ha ι`. Establish `H0 : Good art ι 0 1` using `good_one H`. Establish `key0 : ∀ j : ℕ, Good art ι (fun _ => (j : ℤ)) (cycBar K Ω l ^ j)`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => exact good_cong H0 (funext fun _ => by simp) (pow_zero _).symm`. Consider the case `succ j ih`. Apply the tactic sequence `exact good_cong (good_mul ih H1) (funext fun _ => by simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring) (pow_succ _ _).symm`.

Establish `key : ∀ n : ℕ, Good art ι (fun e => (n : ℤ) * a e + j) (κ ^ n * cycBar K Ω l ^ j)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact good_cong (key0 j) (funext fun _ => by simp) (by simp)`. Consider the case `succ n ih`.

Use `good_cong (good_mul ih H) (funext fun e => ?_) ?_` and prove the remaining obligations. Apply the tactic sequence `simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring`. Rewrite using `[pow_succ]`. Conclude with `mul_right_comm _ _ _`. Conclude with `key n`.
-/
theorem algType_alt (hP : _root_.UpperTheory.V.Af.Hypotheses') : AlgType := by
  intro K Ω _ _ _ _ _ l _ ι art Y a κ ha h1 h2 n j
  have H : Good art ι a κ := ⟨Y, h1, h2⟩
  have H1 : Good art ι (fun _ => 1) (cycBar K Ω l) := good_cyc ha ι
  have H0 : Good art ι 0 1 := good_one H
  have key0 : ∀ j : ℕ, Good art ι (fun _ => (j : ℤ)) (cycBar K Ω l ^ j) := by
    intro j
    induction j with
    | zero => exact good_cong H0 (funext fun _ => by simp) (pow_zero _).symm
    | succ j ih =>
      exact good_cong (good_mul ih H1) (funext fun _ => by simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring)
        (pow_succ _ _).symm
  have key : ∀ n : ℕ, Good art ι (fun e => (n : ℤ) * a e + j) (κ ^ n * cycBar K Ω l ^ j) := by
    intro n
    induction n with
    | zero => exact good_cong (key0 j) (funext fun _ => by simp) (by simp)
    | succ n ih =>
      refine good_cong (good_mul ih H) (funext fun e => ?_) ?_
      · simp only [Pi.add_apply, Nat.cast_add, Nat.cast_one] <;> ring
      · rw [pow_succ]
        exact mul_right_comm _ _ _
  exact key n
end UpperTheory.V.Cu2
end
end
