import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ConnectionKillsSeries
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.CharDepth TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharDepth

/- English proof (translation)
Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul a x`. Establish `h` using `PadicInt.zmodRepr_spec a`. Take `⟨-, h⟩` from `h`.

Rewrite `h` using `[PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton]`. Take `⟨c, hc⟩` from `h`. Use `⟨c ⊗ₜ[ℤ] x, (a.zmodRepr : ℤ) • x, ?_⟩` and prove the remaining obligations. Establish `ha : a = (p : ℕ) • c + (a.zmodRepr : ℤ) • (1 : ℤ_[p])`. Rewrite using `[nsmul_eq_mul, ← hc]`.

Simplify using the standard rewrite rules. Rewrite using `[← nsmul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul, ← ha]`. Consider the case `add a b ha hb`. Take `⟨s, x, rfl⟩` from `ha`. Take `⟨s', x', rfl⟩` from `hb`.

Conclude with `⟨s + s', x + x', by rw [TensorProduct.tmul_add]; ring⟩`.
-/
theorem padicTensor_eq_mul_add (A : Type) [CommRing A] (p : ℕ) [Fact p.Prime]
    (r : ℤ_[p] ⊗[ℤ] A) :
    ∃ (s : ℤ_[p] ⊗[ℤ] A) (x : A), r = (p : ℤ_[p] ⊗[ℤ] A) * s + (1 : ℤ_[p]) ⊗ₜ[ℤ] x := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul a x =>
    have h := PadicInt.zmodRepr_spec a
    obtain ⟨-, h⟩ := h
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at h
    obtain ⟨c, hc⟩ := h
    refine ⟨c ⊗ₜ[ℤ] x, (a.zmodRepr : ℤ) • x, ?_⟩
    have ha : a = (p : ℕ) • c + (a.zmodRepr : ℤ) • (1 : ℤ_[p]) := by
      rw [nsmul_eq_mul, ← hc]; simp
    rw [← nsmul_eq_mul, TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, ← ha]
  | add a b ha hb =>
    obtain ⟨s, x, rfl⟩ := ha
    obtain ⟨s', x', rfl⟩ := hb
    exact ⟨s + s', x + x', by rw [TensorProduct.tmul_add]; ring⟩

end GlobalTheory.CharDepth
