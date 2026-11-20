import Formalism.LocalToGlobal.Columns.TiedXp
import Formalism.LocalToGlobal.Columns.InputsGenus

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `u i` and use `colDecoPtSurj d.sp.cm d.hPr u (d.R.N i) (unimodGenus_holds d.sp.cm (d.R.N i))`.
-/
theorem ptSurj_holds (d : ColDat) : PtSurj d := fun u i =>
  colDecoPtSurj d.sp.cm d.hPr u (d.R.N i) (unimodGenus_holds d.sp.cm (d.R.N i))

/- English proof (translation)
Use `decoPtSurj_of d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs (unimodGenus_holds d.sp.cm _) reduction_surjective_bis ?_ (Finset.disjoint_empty_left _)` and prove the remaining obligations. Introduce `PP hP PP' hP'`. Conclude with `isSplitSet_of_ok d.hPr d.u₀ PP (Finset.mem_union_right _ (by simpa using hP)) PP' (Finset.mem_union_right _ (by simpa using hP'))`.
-/
theorem points_surjective (d : ColDat) : PtSurjP d := by
  classical
  refine decoPtSurj_of d.sp.cm (d.R.N d.R.m - 1) ∅ d.Pr.vGs (unimodGenus_holds d.sp.cm _) reduction_surjective_bis ?_ (Finset.disjoint_empty_left _)
  intro PP hP PP' hP'
  exact isSplitSet_of_ok d.hPr d.u₀ PP (Finset.mem_union_right _ (by simpa using hP)) PP' (Finset.mem_union_right _ (by simpa using hP'))

end Formalism.L2.Col
