import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutFP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GoodAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ hT X j` and use `ParameterFamilyAlgebra.good_fn hT X j`.
-/
theorem good_function_leaf : CutFP.GoodFnLeaf :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hT X j => ParameterFamilyAlgebra.good_fn hT X j

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ _ _ _ _ _ hOm hS X Y a b` and use `ParameterFamilyAlgebra.good_alt_bis hOm hS X Y a b`.
-/
theorem good_transfer_leaf : CutFP.GoodTLeaf :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hOm hS X Y a b => ParameterFamilyAlgebra.good_alt_bis hOm hS X Y a b

/- English proof (translation)
The claim follows from `CutFP.frameParam_of good_function_leaf good_transfer_leaf`.
-/
theorem frame_parameter_regularity : PBI.FrameParam :=
  CutFP.frameParam_of good_function_leaf good_transfer_leaf

end Formalism.FourierDecayAlt.P
