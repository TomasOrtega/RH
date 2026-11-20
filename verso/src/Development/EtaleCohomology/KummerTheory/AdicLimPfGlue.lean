import Development.EtaleCohomology.KummerTheory.AdicLimPfCok

namespace LateralTheory.KummerTheory

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem AdicLim_of_fin (hF : AdicFin) : AdicLim := AdicLim_of AdicKer_holds hF AdicCok_holds

end LateralTheory.KummerTheory
