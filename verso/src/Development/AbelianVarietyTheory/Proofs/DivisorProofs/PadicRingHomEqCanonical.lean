import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[← sub_eq_zero]`. Apply `IsHausdorff.haus (I := Ideal.span {(p : O)}) ‹_›` to reduce the goal to its premises. Introduce `n`. Rewrite using `[SModEq.zero]`.

Take `⟨y, hy⟩` from `Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n x)`. Establish `hx : x = (x.appr n : ℤ_[p]) + y * (p : ℤ_[p]) ^ n` using `by rw [hy]; ring`. Establish `hfx : f x - g x = (f y - g y) * (p : O) ^ n`. Rewrite using `[hx, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, map_natCast, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hfx, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]`. Conclude with `Ideal.mem_span_singleton'.mpr ⟨f y - g y, rfl⟩`.
-/
theorem padicInt_ringHom_ext (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O]
    [IsHausdorff (Ideal.span {(p : O)}) O] (f g : ℤ_[p] →+* O) : f = g := by
  ext x
  rw [← sub_eq_zero]
  apply IsHausdorff.haus (I := Ideal.span {(p : O)}) ‹_›
  intro n
  rw [SModEq.zero]
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp (PadicInt.appr_spec n x)
  have hx : x = (x.appr n : ℤ_[p]) + y * (p : ℤ_[p]) ^ n := by rw [hy]; ring
  have hfx : f x - g x = (f y - g y) * (p : O) ^ n := by
    rw [hx, map_add, map_add, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast,
      map_natCast, map_natCast]
    ring
  rw [hfx, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  exact Ideal.mem_span_singleton'.mpr ⟨f y - g y, rfl⟩

/- English proof (translation)
Introduce `p _ O _ _ _ g`. Conclude with `padicInt_ringHom_ext p O g (padicToO p O)`.
-/
theorem padicToO_unique : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (g : ℤ_[p] →+* O), g = padicToO p O := by
  intro p _ O _ _ _ g
  exact padicInt_ringHom_ext p O g (padicToO p O)

end GlobalTheory
