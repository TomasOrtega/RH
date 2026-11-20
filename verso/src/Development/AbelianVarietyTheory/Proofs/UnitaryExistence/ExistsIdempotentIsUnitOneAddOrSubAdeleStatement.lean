import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentIsUnitOneAddOrSubAdele
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.AdIdem.exists_idem_isUnit` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnitaryExistence%2FExistsIdempotentIsUnitOneAddOrSubAdele.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.exists_idempotent_isUnit_one_add_or_sub_adele : ∀ (F : Type) [Field F] [NumberField F] (s : AdeleRing (𝓞 F) F), ∃ e : AdeleRing (𝓞 F) F, e * e = e ∧ IsUnit (e * (1 + s) + (1 - e) * (1 - s)) := by
  first | exact @GlobalTheory.AdIdem.exists_idem_isUnit | exact GlobalTheory.AdIdem.exists_idem_isUnit | (intros; apply GlobalTheory.AdIdem.exists_idem_isUnit <;> assumption)
