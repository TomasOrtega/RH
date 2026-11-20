import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.GenericPrincipalSeries.GenericPrincipalSeries
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.StrictDominanceCasselman.IsStrictlyDominant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GeneralizedEigenvectorExistsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetCuspidalSupportOfFunctionalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusReciprocityNonzero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetModuleAdmissibleFixedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetVectorFixedDeepLevelStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DeepLevelSubgroupsFiltrationStatement

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil ValuativeRel

namespace GlobalTheory.CompanionTheory.PinLift

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Establish `hi : i = 0` using `Subsingleton.elim _ _`. Establish `hj : j = 0` using `Subsingleton.elim _ _`. Substitute `hi` using the available equality.

Substitute `hj` using the available equality. Simplify using `only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one]`. Conclude with `mul_comm _ _`.
-/
theorem gl_one_comm {k : Type} [Field k] (a b : GL (Fin 1) k) : a * b = b * a := by
  apply Units.ext
  ext i j
  have hi : i = 0 := Subsingleton.elim _ _
  have hj : j = 0 := Subsingleton.elim _ _
  subst hi
  subst hj
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_one]
  exact mul_comm _ _

noncomputable def torusCharHom {k : Type} [Field k] {n : ℕ} (ξ : Fin n → (kˣ →* ℂˣ)) :
    (∀ _ : Fin n, GL (Fin 1) k) →* ℂ where
  toFun := PositivityTheory.Lbc.torusChar ξ
  map_one' := by simp [PositivityTheory.Lbc.torusChar]
  map_mul' a b := by simp [PositivityTheory.Lbc.torusChar, Finset.prod_mul_distrib]

end GlobalTheory.CompanionTheory.PinLift
