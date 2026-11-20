import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl

namespace GlobalTheory.CompanionTheory.Ar.Fl

/- English proof (translation)
Set `_ : Algebra k k'` to `f.toAlgebra`. Set `_ : Algebra k A` to `j.toAlgebra`. Establish `: IsScalarTower ℚ k k'` using `IsScalarTower.of_algebraMap_eq fun q => by`. Rewrite using `[RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ k') q, eq_ratCast (algebraMap ℚ k) q, map_ratCast]`. Establish `: Module.Finite k k'` using `Module.Finite.of_restrictScalars_finite ℚ k k'`.

Establish `: Algebra.IsAlgebraic k k'` using `Algebra.IsAlgebraic.of_finite k k'`. Use `⟨(IsAlgClosed.lift : k' →ₐ[k] A).toRingHom, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Conclude with `(IsAlgClosed.lift : k' →ₐ[k] A).commutes x`.
-/
theorem exists_comp_eq_of_numberField (k k' A : Type) [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field A] [CharZero A] [IsAlgClosed A] (f : k →+* k') (j : k →+* A) :
    ∃ j' : k' →+* A, j'.comp f = j := by
  let _ : Algebra k k' := f.toAlgebra
  let _ : Algebra k A := j.toAlgebra
  have : IsScalarTower ℚ k k' := IsScalarTower.of_algebraMap_eq fun q => by
    rw [RingHom.algebraMap_toAlgebra, eq_ratCast (algebraMap ℚ k') q, eq_ratCast (algebraMap ℚ k) q,
      map_ratCast]
  have : Module.Finite k k' := Module.Finite.of_restrictScalars_finite ℚ k k'
  have : Algebra.IsAlgebraic k k' := Algebra.IsAlgebraic.of_finite k k'
  refine ⟨(IsAlgClosed.lift : k' →ₐ[k] A).toRingHom, ?_⟩
  ext x
  exact (IsAlgClosed.lift : k' →ₐ[k] A).commutes x

end GlobalTheory.CompanionTheory.Ar.Fl
