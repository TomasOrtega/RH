import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCyclic
import Formalism.SharpRestriction.LevelLetterCocycles.ProdOneSubPrimitiveRoots
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.LiftKur

/- English proof (translation)
Introduce `l _ x y hy`. Use `haveI : Algebra.IsAlgebraic ↥(MaximalUnramifiedExtension l) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) ↥(MaximalUnramifiedExtension l)`. Use `haveI : IsAlgClosure ↥(MaximalUnramifiedExtension l) (Om l) := ⟨inferInstance, inferInstance⟩`. Use `haveI : Normal ↥(MaximalUnramifiedExtension l) (Om l) := IsAlgClosure.normal _ _`. Establish `hx : IsIntegral ↥(MaximalUnramifiedExtension l) x` using `Algebra.IsIntegral.isIntegral x`.

Establish `hmin : minpoly ↥(MaximalUnramifiedExtension l) x = minpoly ↥(MaximalUnramifiedExtension l) y` using `(minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy (minpoly.monic hx))`. Take `⟨τ, hτ⟩` from `(Normal.minpoly_eq_iff_mem_orbit (F := ↥(MaximalUnramifiedExtension l)) (E := Om l) (x := y) (y := x)).1 hmin.symm`. Use `⟨τ.restrictScalars ℚ_[l], ?_, ?_⟩` and prove the remaining obligations. Introduce `z hz show τ z = z`. Conclude with `τ.commutes ⟨z, hz⟩`.

Use `show τ x = y`. Conclude with `hτ`.
-/
theorem exists_gal_fix_Kur_map : ∀ (l : ℕ) [Fact l.Prime] (x y : Om l), Polynomial.aeval y (minpoly ↥(MaximalUnramifiedExtension l) x) = 0 → ∃ g : GQ l, (∀ z ∈ MaximalUnramifiedExtension l, g z = z) ∧ g x = y := by
  intro l _ x y hy
  haveI : Algebra.IsAlgebraic ↥(MaximalUnramifiedExtension l) (Om l) := Algebra.IsAlgebraic.tower_top (K := ℚ_[l]) ↥(MaximalUnramifiedExtension l)
  haveI : IsAlgClosure ↥(MaximalUnramifiedExtension l) (Om l) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ↥(MaximalUnramifiedExtension l) (Om l) := IsAlgClosure.normal _ _
  have hx : IsIntegral ↥(MaximalUnramifiedExtension l) x := Algebra.IsIntegral.isIntegral x
  have hmin : minpoly ↥(MaximalUnramifiedExtension l) x = minpoly ↥(MaximalUnramifiedExtension l) y :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) hy (minpoly.monic hx))
  obtain ⟨τ, hτ⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := ↥(MaximalUnramifiedExtension l)) (E := Om l) (x := y) (y := x)).1 hmin.symm
  refine ⟨τ.restrictScalars ℚ_[l], ?_, ?_⟩
  · intro z hz
    show τ z = z
    exact τ.commutes ⟨z, hz⟩
  · show τ x = y
    exact hτ

end GlobalTheory.LiftKur
