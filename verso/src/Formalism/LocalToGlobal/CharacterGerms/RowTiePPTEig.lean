import Formalism.LocalToGlobal.CharacterGerms.RowTiePPTSelfClose
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLieSelf
import Formalism.LocalToGlobal.CharacterGerms.ProjFBOfEig

namespace Formalism.L2.FormalSeriesBounds

/- English proof (translation)
The claim follows from `ptFB_of_proj2 (RowTiePProj.projFB_of RowTiePLSmall.lSmall_holds (RowTiePLie.projLie_of (RowTiePKey.key_of hE RowTiePKeyRes.keyRes_holds RowTiePKey.keyDelta_holds) RowTiePSplit.split_holds))`.
-/
theorem ptFB_of_eig (hE : RowTiePKey.KeyEigSt) : PTFBSt :=
  ptFB_of_proj2 (RowTiePProj.projFB_of RowTiePLSmall.lSmall_holds
    (RowTiePLie.projLie_of (RowTiePKey.key_of hE RowTiePKeyRes.keyRes_holds RowTiePKey.keyDelta_holds)
      RowTiePSplit.split_holds))

/- English proof (translation)
The claim follows from `cartFB_of_proj2 (RowTiePProj.projFB_of RowTiePLSmall.lSmall_holds (RowTiePLie.projLie_of (RowTiePKey.key_of hE RowTiePKeyRes.keyRes_holds RowTiePKey.keyDelta_holds) RowTiePSplit.split_holds))`.
-/
theorem cartFB_of_eig (hE : RowTiePKey.KeyEigSt) : CartFBSt :=
  cartFB_of_proj2 (RowTiePProj.projFB_of RowTiePLSmall.lSmall_holds
    (RowTiePLie.projLie_of (RowTiePKey.key_of hE RowTiePKeyRes.keyRes_holds RowTiePKey.keyDelta_holds)
      RowTiePSplit.split_holds))

/- English proof (translation)
The claim follows from `ptSelf_of_start2 (allStartSelf_of_eig hE)`.
-/
theorem ptSelf_of_eig (hE : RowTiePKey.KeyEigSt) : PTSelfSt :=
  ptSelf_of_start2 (allStartSelf_of_eig hE)

end Formalism.L2.FormalSeriesBounds
