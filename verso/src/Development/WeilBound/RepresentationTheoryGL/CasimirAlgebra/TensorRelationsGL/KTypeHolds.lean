import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGl
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PCurry
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PJmComm
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PPiQdet
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepFormula
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PQdetFacts
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallQuot
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PStepChar
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSpectrum
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PHeight
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PChain
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PColAnti
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransFin
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransOf
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTransAll
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PWallAlg
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PTensorGK
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PLieInv
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSemiZero
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PSWStart
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PContract
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PYoung
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.PKType

namespace PositivityTheory.Rg.Cz

/- English proof (translation)
Establish `tg` using `tensorGl_holds`. Establish `jm` using `jmComm_of tg`. Establish `cu` using `curry_holds`. Establish `qd` using `qdetFacts_holds`. Establish `pq` using `piQdet_of tg jm`.

Establish `sf` using `stepFormula_of tg jm pq cu`. Establish `sc` using `stepChar_of tg sf qd`. Establish `sp` using `spectrum_of tg jm cu sc`. Establish `ht` using `height_of tg`. Establish `wq` using `wallQuot_of qd`.

Establish `ch` using `chain_of tg jm cu sf qd sc ht wq`. Establish `ca` using `colAnti_of tg jm ht`. Establish `tf` using `transFin_of tg jm sf qd sp ch ca`. Establish `tr` using `trans_of tf`. Establish `ta` using `transAll_of tg tr`.

Establish `tk` using `tensorGK_of tg`. Establish `wa` using `wallAlg_of tg jm qd sp`. Establish `li` using `lieInv_holds`. Establish `co` using `contract_of tg qd wa tk li wq`. Establish `sz` using `semiZero_of qd wa li wq`.

Establish `sa` using `sphAll_of swStart_holds co sz`. Conclude with `kType_of tg ta tk sa young_holds`.
-/
theorem kType_holds : KType := by
  have tg := tensorGl_holds
  have jm := jmComm_of tg
  have cu := curry_holds
  have qd := qdetFacts_holds
  have pq := piQdet_of tg jm
  have sf := stepFormula_of tg jm pq cu
  have sc := stepChar_of tg sf qd
  have sp := spectrum_of tg jm cu sc
  have ht := height_of tg
  have wq := wallQuot_of qd
  have ch := chain_of tg jm cu sf qd sc ht wq
  have ca := colAnti_of tg jm ht
  have tf := transFin_of tg jm sf qd sp ch ca
  have tr := trans_of tf
  have ta := transAll_of tg tr
  have tk := tensorGK_of tg
  have wa := wallAlg_of tg jm qd sp
  have li := lieInv_holds
  have co := contract_of tg qd wa tk li wq
  have sz := semiZero_of qd wa li wq
  have sa := sphAll_of swStart_holds co sz
  exact kType_of tg ta tk sa young_holds

end PositivityTheory.Rg.Cz
