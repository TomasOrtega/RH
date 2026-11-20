import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.KunnethLefschetz.EtaleCharts.BlowOfBl
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.IsIntegralOfNormLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.EqOneOfNear

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.KunnethLefschetz.G.oKDvr :
    UpperTheory.Gal.KunnethLefschetz.G.OKDvr := by
  intro l _ K _
  have hK : (CrystallineSemistableComparison.OK l K) = (integralClosure ℤ_[l] K).toSubring := by
    ext x
    constructor
    · intro hx
      have h1 : ‖(x : PadicAlgCl l)‖ ≤ 1 := hx
      have h2 : IsIntegral ℤ_[l] (x : PadicAlgCl l) := UpperTheory.V.Lib.Small.isIntegral_of_norm_le h1
      exact (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).1 h2
    · intro hx
      have h2 : IsIntegral ℤ_[l] (x : PadicAlgCl l) := IsIntegral.map (K.val.restrictScalars ℤ_[l]) hx
      exact UpperTheory.V.Lib.Small.norm_le_one_of_isIntegral l _ h2
  rw [hK]
  exact (IsIntegralClosure.isNoetherianRing ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K))
