import Development.WeilBound.ThetaLifts.TowerModels.TowerCodimensionTwoOf
import Development.WeilBound.ThetaLifts.TowerModels.LeviEx
import Development.WeilBound.ThetaLifts.TowerModels.PlaneSkew
import Development.WeilBound.ThetaLifts.TowerModels.StabEx
import Development.WeilBound.ThetaLifts.TowerModels.ModelEx
import Development.WeilBound.ThetaLifts.TowerModels.WeilExOf

noncomputable section

namespace PositivityTheory.ThKG.Tow

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

/- English proof (translation)
Assemble the required witnesses or components as `⟨planeHerm, planeSkew⟩`.
-/
theorem planeEx : PlaneEx := ⟨planeHerm, planeSkew⟩

/- English proof (translation)
The claim follows from `pairEx_of modelEx (weilEx_of h)`.
-/
theorem pairEx (h : WeilPairExists) : PairEx := pairEx_of modelEx (weilEx_of h)

end PositivityTheory.ThKG.Tow

end
