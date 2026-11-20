import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

def extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type} [Group G] {n : ℕ}
    (ρ : Representation K G (Fin n → K)) : Representation L G (Fin n → L) where
  toFun g := Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L))
  map_one' := by
    rw [map_one, LinearMap.toMatrix'_one, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.toLin'_one]
    rfl
  map_mul' g h := by
    rw [map_mul, LinearMap.toMatrix'_mul, Matrix.map_mul, Matrix.toLin'_mul]
    rfl

/- English proof (translation)
Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Establish an intermediate fact. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem character_extendScalarsRep (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type}
    [Group G] {n : ℕ} (ρ : Representation K G (Fin n → K)) (g : G) :
    (extendScalarsRep K L ρ).character g = algebraMap K L (ρ.character g) := by
  have h1 : (extendScalarsRep K L ρ).character g
      = ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L)).trace := by
    change LinearMap.trace L _ (Matrix.toLin' _) = _
    exact Matrix.trace_toLin'_eq _
  have h2 : ρ.character g = (LinearMap.toMatrix' (ρ g)).trace := by
    change LinearMap.trace K _ (ρ g) = _
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  rw [h1, h2]
  simp [Matrix.trace, map_sum]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.
-/
theorem isChar_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (G : Type) [Group G]
    (χ : G → L), IsChar K L χ → IsChar L L χ := by
  intro K L _ _ _ G _ χ ⟨n, ρ, h⟩
  refine ⟨n, extendScalarsRep K L ρ, fun g => ?_⟩
  rw [h g, character_extendScalarsRep]
  rfl

end GlobalTheory.BI
