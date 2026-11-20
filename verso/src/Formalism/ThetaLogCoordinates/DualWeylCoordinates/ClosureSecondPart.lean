import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.StripDataTensorColumnFamilies
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.CntSym
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.CntLam
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.SymStrip
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.SymDStrip
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.LamStrip

namespace Formalism.InvariantFactorPaths.ColumnFamilies.Top

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem strip_data_tensor_column_families : StripDataTensorColumnFamilies := strip_data_tensor_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem symStrip : SymStrip := symStrip_of symmetric_power_count_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem symDStrip : SymDStrip := symDStrip_of dual_symmetric_power_count_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lamStrip : LamStrip := lamStrip_of exterior_power_count_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem closure_second_part : ClosureTensorPowers := closure_tensor_of_strip_data strip_data_tensor_column_families symStrip symDStrip lamStrip

end Formalism.InvariantFactorPaths.ColumnFamilies.Top
