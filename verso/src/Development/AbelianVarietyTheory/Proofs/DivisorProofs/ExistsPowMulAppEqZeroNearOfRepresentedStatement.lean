import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowMulAppEqZeroNearOfRepresented
import Mathlib
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPowMulAppEqZeroNearOfRepresented.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.exists_pow_mul_app_eq_zero_near_of_represented' : ∀ (S : Scheme.{0}) (Φ : ∀ (T : Scheme.{0}), (T ⟶ S) → Prop), (∀ (T T' : Scheme.{0}) (t : T ⟶ S) (u : T' ⟶ T), Φ T t → Φ T' (u ≫ t)) → ∀ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), IsClosedImmersion i → (∀ (T : Scheme.{0}) (t : T ⟶ U), Φ T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t) → ∀ (W : S.Opens) (s c : Γ(S, W)), (∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app (S.basicOpen s)).hom ((S.presheaf.map (homOfLE (S.basicOpen_le s)).op).hom c) = 0) → ∀ y : S, y ∈ U → y ∈ W → ∃ (V : S.Opens) (hV : V ≤ W), y ∈ V ∧ ∃ n : ℕ, ∀ (T : Scheme.{0}) (t : T ⟶ S), Φ T t → (t.app V).hom ((S.presheaf.map (homOfLE hV).op).hom (s ^ n * c)) = 0 := by
  first | exact @GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented | exact GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented | (intros; apply GlobalTheory.exists_pow_mul_app_eq_zero_near_of_represented; all_goals assumption)
