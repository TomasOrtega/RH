import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockIndexMonotone

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

/- English proof (translation)
Introduce `R _ N s d hd h hh`. Establish `hp : h ∈ parab R (stdBlocks d hd)`. Rewrite using `[mem_parab_iff]`. Introduce `a b i j hba`. Conclude with `hh _ _ (GlobalTheory.CompanionTheory.BlockIndex.stdBlocks_lt_of_lt d hd hba i j)`.

Use `⟨hp, fun a => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular]`. Apply `Finset.prod_congr rfl` to reduce the goal to its premises. Introduce `j _`. Conclude with `leviProj_apply R (stdBlocks d hd) ⟨h, hp⟩ a j j`.

Introduce `i j hij`. Rewrite using `[leviProj_apply]`. Apply `hh` to reduce the goal to its premises. Establish `hij' : (j : ℕ) < (i : ℕ)` using `hij`. Rewrite using `[Fin.lt_def, stdBlocks_val, stdBlocks_val]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Gal.TypesAndIwahori.finTri :
    UpperTheory.Gal.TypesAndIwahori.FinTri := by
  intro R _ N s d hd h hh
  have hp : h ∈ parab R (stdBlocks d hd) := by
    rw [mem_parab_iff]
    intro a b i j hba
    exact hh _ _ (GlobalTheory.CompanionTheory.BlockIndex.stdBlocks_lt_of_lt d hd hba i j)
  refine ⟨hp, fun a => ?_⟩
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_of_upperTriangular]
  · apply Finset.prod_congr rfl
    intro j _
    exact leviProj_apply R (stdBlocks d hd) ⟨h, hp⟩ a j j
  · intro i j hij
    rw [leviProj_apply]
    apply hh
    have hij' : (j : ℕ) < (i : ℕ) := hij
    rw [Fin.lt_def, stdBlocks_val, stdBlocks_val]
    omega
