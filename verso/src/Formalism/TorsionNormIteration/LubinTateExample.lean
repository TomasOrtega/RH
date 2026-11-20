import Formalism.TorsionNormIteration.InverseIntegralClasses.SolveExistsProof
import Formalism.TorsionNormIteration.InverseIntegralClasses.InvInt
import Formalism.TorsionNormIteration.InverseIntegralClasses.SigmaNormLeOne
import Formalism.TorsionNormIteration.InverseIntegralClasses.MemSpanOfNormLe
import Formalism.TorsionNormIteration.InverseIntegralClasses.NormSigmaLeOne
import Formalism.TorsionNormIteration.InverseIntegralClasses.MapSubtypeInjective
import Formalism.TorsionNormIteration.InverseIntegralClasses.CoeffSubstAddCMulXPow
import Formalism.TorsionNormIteration.InverseIntegralClasses.IsHomOfSubstEqSmul
import Formalism.TorsionNormIteration.InverseIntegralClasses.TorsionNormIterProof
import Formalism.TorsionNormIteration.InverseIntegralClasses.NormNatCastOfNotDvd
import Formalism.TorsionNormIteration.InverseIntegralClasses.LTLemma

namespace Formalism.LT

universe u v

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem funEqSubst : Formalism.G.FunEqSubst.{u, v} :=
  FunEqSubst_of IntegralSubst_proof CoeffBound_valid PowCongr_valid FrobCongr_valid

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem funEqGroup : Formalism.G.FunEqGroup.{u} :=
  FunEqGroup_of SolveExists_proof InvIntegralOfClass_proof FunEqLowCoeff_proof funEqSubst

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem funEqFormalGroup : Formalism.G.FunEqFormalGroup.{u} := FunEqFormalGroup_of funEqGroup

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem funEqHom : Formalism.G.FunEqHom.{u} :=
  FunEqHom_of SolveExists_proof InvIntegralOfClass_proof FunEqLowCoeff_proof funEqSubst

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem funEqCongr : Formalism.G.FunEqCongr.{u} := FunEqCongr_of CoeffBound_valid PowCongr_valid

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lubinTateExample : Formalism.G.LubinTateExample :=
  LubinTateExample_of funEqFormalGroup funEqHom funEqCongr

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Evaluate the numerical expressions. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Evaluate the numerical expressions.
-/
theorem torsionExample : TorsionExample := by
  unfold TorsionExample IsLTPoly
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp
  · simp [Polynomial.coeff_X]
  · simp [Polynomial.coeff_X]
  · intro i h1 h2
    simp [Polynomial.coeff_X, Polynomial.coeff_X_pow, h2, Ne.symm h1]
  · norm_num
  · have h : ‖((2 : ℕ) : ℚ_[2])‖ < 1 := Padic.norm_p_lt_one
    simpa using h
  · norm_num
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expIntegral : ExpIntegral.{u} := exp_integral

end Formalism.LT
