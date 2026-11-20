import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsPullHermPullLine
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedA
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict

/- English proof (translation)
Introduce `m n`. Use `⟨fun _ _ => 1, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i j c`. Simplify using `only [map_one, mul_one]`. Conclude with `(map_one (Semi.res _)).symm`.

Introduce `i c c'`. Simplify using `[GlobalTheory.CompanionTheory.Ar.Top.trivLine]`. Introduce `i c y z _ hy`. Establish `e : CxPts.ev (mpStr ℤ m n) σ₀ ((HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c) (((1 : Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)ˣ)) : Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)) y = 1`. Rewrite using `[CxPts.ev_eq hy, Units.val_one, map_one]`.

Rewrite using `[e]`. Simplify using `[GlobalTheory.CompanionTheory.Ar.Top.trivLine, HermLB.triv, Weight.ofFun]`.
-/
theorem isHermRep_triv : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ), IsHermRep (HermLB.triv (mpStr ℤ m n)) (GlobalTheory.CompanionTheory.Ar.Top.trivLine (Bk n)) := by
  intro m n
  refine ⟨fun _ _ => 1, ?_, ?_, ?_⟩
  · intro i j c
    simp only [map_one, mul_one]
    exact (map_one (Semi.res _)).symm
  · intro i c c'
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine]
  · intro i c y z _ hy
    have e : CxPts.ev (mpStr ℤ m n) σ₀ ((HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)
        (((1 : Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)ˣ)) :
          Γ(MP ℤ m n, (HermLB.triv (mpStr ℤ m n)).B.U i ⊓ mchart c)) y = 1 := by
      rw [CxPts.ev_eq hy, Units.val_one, map_one]
    rw [e]
    simp [GlobalTheory.CompanionTheory.Ar.Top.trivLine, HermLB.triv, Weight.ofFun]

end GlobalTheory.CompanionTheory.MPDict
