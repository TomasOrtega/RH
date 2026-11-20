import Development.EtaleCohomology.EtaleSheaves.KernelLocalization.RangeOfBd
import Development.EtaleCohomology.EtaleSheaves.TruncKerPf
import Development.EtaleCohomology.EtaleSheaves.LocalDescent.DescLocOf
import Development.EtaleCohomology.EtaleSheaves.FiltrationLevelInjectivity
import Development.EtaleCohomology.EtaleSheaves.CechLevelIsomorphism

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.LeafGhostCut
/- English proof (translation)
Introduce `hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y ⟨x, hx⟩`. Establish `hinj` using `hD hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo'`. Use `LateralTheory.E.KernelLocalization.range_of_bd _ _ _ m n (by omega) y ((injective_iff_map_eq_zero _).1 hinj _ ?_)` and prove the remaining obligations. Use `(LateralTheory.E.KernelLocalization.rpull_bd ..).trans ?_` and prove the remaining obligations. Rewrite using `[← hx]`.

Conclude with `LateralTheory.E.KernelLocalization.bd_pull ..`.
-/
theorem LateralTheory.E.TruncationCokernelLevelRelations.TruncCok_of (hD : LateralTheory.E.TruncationKernel.RelDesc) : LateralTheory.E.DescLocPf.Fine.TruncCok := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' m hm y ⟨x, hx⟩
  have hinj := hD hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo'
  refine LateralTheory.E.KernelLocalization.range_of_bd _ _ _ m n (by omega) y ((injective_iff_map_eq_zero _).1 hinj _ ?_)
  refine (LateralTheory.E.KernelLocalization.rpull_bd ..).trans ?_
  rw [← hx]
  exact LateralTheory.E.KernelLocalization.bd_pull ..
/- English proof (translation)
Introduce `hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' p _ m hm`. Establish `h` using `LateralTheory.E.LevelsPf.Tp.Levels_of' LateralTheory.E.CechLevelIsoPf.CechLevelIso_of hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm`. Conclude with `⟨h.2, h.1 (m - 1) (by omega)⟩`.
-/
theorem LateralTheory.E.TruncationCokernelLevelRelations.LvlRel_of : LateralTheory.E.FiltrationLevelInjectivity.LvlRel := by
  intro hH q _ i n A Y φ hq P hpush het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' he hs hE hpo' p _ m hm
  have h := LateralTheory.E.LevelsPf.Tp.Levels_of' LateralTheory.E.CechLevelIsoPf.CechLevelIso_of hH q i n φ hq P @hpush @het hlow D d hPD Y' w φ' hpo E e Y'' u φ'' hpo' he hs hE p m hm
  exact ⟨h.2, h.1 (m - 1) (by omega)⟩
