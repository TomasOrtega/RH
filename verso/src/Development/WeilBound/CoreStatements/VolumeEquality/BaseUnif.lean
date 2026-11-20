import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifAsm
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifConj
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifCoord
import Development.WeilBound.CoreStatements.VolumeEquality.BaseUnifVec

namespace SheetDecomposition

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem baseUnifEx2 : BaseUnifEx2 := baseUnifEx2_of (vecOfPeriods_of holCoord) kUnifConj

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem baseUnifEx : BaseUnifEx := fun hG E _ _ _ H D l Xo c Y sm j j' n h₁ h₂ h₃ =>
  (baseUnifEx2 hG E H D l Xo c Y sm j j' n h₁ h₂ h₃).elim fun B _ => ⟨B⟩

end SheetDecomposition
