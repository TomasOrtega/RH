import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneTmulMemRangeIff
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CovOfAlgHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPQ
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrobeniusPowerSolutionLiftStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PerfectFrobeniusRootSolutionStatement
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovRoot

/- English proof (translation)
Set `b` to `AdjoinRoot.powerBasis' hP`. Establish `h0 : 0 < b.dim` using `by simpa [b] using hd`. Use `⟨b.basis.coord ⟨0, h0⟩, ?_⟩` and prove the remaining obligations. Establish `h1 : b.basis ⟨0, h0⟩ = 1` using `by simp`. Express the relevant statement in the definitionally equal form `b.basis.repr 1 ⟨0, h0⟩ = 1`.

Rewrite using `[← h1, b.basis.repr_self]`. Simplify using the standard rewrite rules.
-/
theorem exists_retraction {A : Type} [CommRing A] (P : Polynomial A) (hP : P.Monic)
    (hd : 0 < P.natDegree) : ∃ ρ : AdjoinRoot P →ₗ[A] A, ρ 1 = 1 := by
  let b := AdjoinRoot.powerBasis' hP
  have h0 : 0 < b.dim := by simpa [b] using hd
  refine ⟨b.basis.coord ⟨0, h0⟩, ?_⟩
  have h1 : b.basis ⟨0, h0⟩ = 1 := by simp
  change b.basis.repr 1 ⟨0, h0⟩ = 1
  rw [← h1, b.basis.repr_self]
  simp

/- English proof (translation)
Introduce `p _ A _ r P hA hP hd`. Establish `hpS : (p : AdjoinRoot P) = 0`. Use `congrArg (algebraMap A (AdjoinRoot P)) hA.char` as an intermediate fact. Simplify using `using this`. Take `⟨T, _, i, hq⟩` from `GlobalTheory.CompanionTheory.PerfClos.exists_PQ p (AdjoinRoot P) ⊥ hpS`.

Use `letI : Algebra A T := (i.comp (algebraMap A (AdjoinRoot P))).toAlgebra`. Set `i' : AdjoinRoot P →ₐ[A] T` to `{ i with commutes' := fun _ => rfl }`. Establish `hq' : PQ p (i' : AdjoinRoot P →+* T) ⊥` using `hq`. Use `⟨T, inferInstance, inferInstance, hq.pf, ?_, i' (AdjoinRoot.root P), ?_⟩` and prove the remaining obligations. Use `GlobalTheory.CompanionTheory.CovCmp.cov_of_solv p A T r fun m n a c hs => ?_` and prove the remaining obligations.

Use `⟨A, inferInstance, inferInstance, GlobalTheory.CompanionTheory.CovMono.cov_self p A r, ?_⟩` and prove the remaining obligations. Take `⟨k, s, hs'⟩` from `GlobalTheory.T.frobenius_power_solution_lift p A (AdjoinRoot P) T i' ⊥ m n a c hA.char hq' hs`. Use `GlobalTheory.T.perfect_frobenius_root_solution p A A m n k a c hA ?_` and prove the remaining obligations. Take `⟨ρ, hρ⟩` from `exists_retraction P hP hd`. Establish `hρa : ∀ x : A, ρ (algebraMap A (AdjoinRoot P) x) = x` using `fun x => by`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, map_smul, hρ, smul_eq_mul, mul_one]`. Use `⟨fun j => ρ (s j), fun t => ?_⟩` and prove the remaining obligations. Establish `h` using `sub_eq_zero.mp ((Ideal.mem_bot).mp (hs' t))`. Establish `h2` using `congrArg ρ h`. Rewrite `h2` using `[map_sum, hρa]`.

Simplify using `using h2`. Rewrite using `[Polynomial.aeval_algHom_apply]`. Establish `: Polynomial.aeval (AdjoinRoot.root P) P = 0`. Simplify using `[AdjoinRoot.aeval_eq]`. Rewrite using `[this, map_zero]`.
-/
theorem cov_root : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A)
    (P : Polynomial A), Pf p A → P.Monic → 0 < P.natDegree →
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
      ∃ x : B, Polynomial.aeval x P = 0 := by
  intro p _ A _ r P hA hP hd
  have hpS : (p : AdjoinRoot P) = 0 := by
    have := congrArg (algebraMap A (AdjoinRoot P)) hA.char
    simpa using this
  obtain ⟨T, _, i, hq⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p (AdjoinRoot P) ⊥ hpS
  letI : Algebra A T := (i.comp (algebraMap A (AdjoinRoot P))).toAlgebra
  let i' : AdjoinRoot P →ₐ[A] T := { i with commutes' := fun _ => rfl }
  have hq' : PQ p (i' : AdjoinRoot P →+* T) ⊥ := hq
  refine ⟨T, inferInstance, inferInstance, hq.pf, ?_, i' (AdjoinRoot.root P), ?_⟩
  · refine GlobalTheory.CompanionTheory.CovCmp.cov_of_solv p A T r fun m n a c hs => ?_
    refine ⟨A, inferInstance, inferInstance, GlobalTheory.CompanionTheory.CovMono.cov_self p A r, ?_⟩
    obtain ⟨k, s, hs'⟩ := GlobalTheory.T.frobenius_power_solution_lift p A (AdjoinRoot P) T i' ⊥ m n a c hA.char hq' hs
    refine GlobalTheory.T.perfect_frobenius_root_solution p A A m n k a c hA ?_
    obtain ⟨ρ, hρ⟩ := exists_retraction P hP hd
    have hρa : ∀ x : A, ρ (algebraMap A (AdjoinRoot P) x) = x := fun x => by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hρ, smul_eq_mul, mul_one]
    refine ⟨fun j => ρ (s j), fun t => ?_⟩
    have h := sub_eq_zero.mp ((Ideal.mem_bot).mp (hs' t))
    have h2 := congrArg ρ h
    rw [map_sum, hρa] at h2
    simpa using h2
  · rw [Polynomial.aeval_algHom_apply]
    have : Polynomial.aeval (AdjoinRoot.root P) P = 0 := by
      simp [AdjoinRoot.aeval_eq]
    rw [this, map_zero]

end GlobalTheory.CompanionTheory.CovRoot
