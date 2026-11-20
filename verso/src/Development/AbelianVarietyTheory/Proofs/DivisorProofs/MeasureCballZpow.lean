import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GindikinKarpelevich
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnramifiedDoublingSumGLConvergentLValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpecialLinearGeneratedByTransvections
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell

namespace GlobalTheory.OrdShellInt

end GlobalTheory.OrdShellInt

namespace GlobalTheory.OrdShellInt

def wt (q : ℝ) : ℕ → ℝ
  | 0 => 1
  | m + 1 => q ^ (m + 1) - q ^ m

end GlobalTheory.OrdShellInt

namespace GlobalTheory.OrdShellInt

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Unfold `ord`. Use `set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k`. Rewrite using `[neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp), map_le_map_iff]`.
-/
theorem val_le_iff_ord (x s : kˣ) : valuation k (x : k) ≤ valuation k (s : k) ↔ ord k s ≤ ord k x := by
  unfold ord
  set φ := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt k
  rw [neg_le_neg_iff, WithZero.log_le_log (by simp) (by simp), map_le_map_iff]

/- English proof (translation)
Set `o : kˣ →* Multiplicative ℤ` to `MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by`. Rewrite using `[ord_mul, ofAdd_add]`. Establish `h` using `map_zpow o x n`. Establish `h2 : Multiplicative.toAdd (o (x ^ n)) = Multiplicative.toAdd ((o x) ^ n)` using `by rw [h]`. Simplify `h2` using `[o, toAdd_zpow]`.
-/
theorem ord_zpow (x : kˣ) (n : ℤ) : ord k (x ^ n) = n * ord k x := by
  let o : kˣ →* Multiplicative ℤ := MonoidHom.mk' (fun x => .ofAdd (ord k x)) fun x y => by
    rw [ord_mul, ofAdd_add]
  have h := map_zpow o x n
  have h2 : Multiplicative.toAdd (o (x ^ n)) = Multiplicative.toAdd ((o x) ^ n) := by rw [h]
  simpa [o, toAdd_zpow] using h2

end GlobalTheory.OrdShellInt

namespace GlobalTheory.OrdShellInt

open ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable [MeasurableSpace k] [BorelSpace k]

end GlobalTheory.OrdShellInt

namespace GlobalTheory.OrdShellInt

open ValuativeRel

end GlobalTheory.OrdShellInt
