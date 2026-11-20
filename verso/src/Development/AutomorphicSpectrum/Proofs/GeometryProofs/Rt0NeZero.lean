import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp

namespace GlobalTheory.CompanionTheory.Ar.Cusp.FamEx

/- English proof (translation)
Establish `hsq` using `H.sqrt_neg_disc_sq`. Establish `hd : (H.d : ℝ) ≠ 0` using `by exact_mod_cast H.d_prime.ne_zero`. Establish `him` using `congrArg Complex.im hsq`. Establish `hre` using `congrArg Complex.re hsq`. Simplify using `only [sq, Complex.mul_im, Complex.mul_re, Complex.neg_im, Complex.neg_re, Complex.natCast_im, Complex.natCast_re] at him hre`.

Establish `h0 : H.rt0.re = 0`. Assume the negation of the conclusion as `h`. Establish `hi : H.rt0.im = 0`. Establish `: H.rt0.re * H.rt0.im = 0` using `by nlinarith`. Conclude with `(mul_eq_zero.1 this).resolve_left h`.

Rewrite `hre` using `[hi]`. Establish `: (0 : ℝ) < H.d` using `lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hd)`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Apply the tactic sequence `apply Complex.ext <;> simp [h0]`.
-/
theorem rt0_conj_neg_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have hsq := H.sqrt_neg_disc_sq
  have hd : (H.d : ℝ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  have him := congrArg Complex.im hsq
  have hre := congrArg Complex.re hsq
  simp only [sq, Complex.mul_im, Complex.mul_re, Complex.neg_im, Complex.neg_re, Complex.natCast_im,
    Complex.natCast_re] at him hre
  have h0 : H.rt0.re = 0 := by
    by_contra h
    have hi : H.rt0.im = 0 := by
      have : H.rt0.re * H.rt0.im = 0 := by nlinarith
      exact (mul_eq_zero.1 this).resolve_left h
    rw [hi] at hre
    have : (0 : ℝ) < H.d := lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hd)
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext <;> simp [h0]

/- English proof (translation)
Introduce `h`. Establish `hsq` using `H.sqrt_neg_disc_sq`. Rewrite `hsq` using `[h]`. Establish `hd : (H.d : ℂ) ≠ 0` using `by exact_mod_cast H.d_prime.ne_zero`. Simplify using `at hsq`.

Conclude with `H.d_prime.ne_zero hsq`.
-/
theorem rt0_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) : H.rt0 ≠ 0 := by
  intro h
  have hsq := H.sqrt_neg_disc_sq
  rw [h] at hsq
  have hd : (H.d : ℂ) ≠ 0 := by exact_mod_cast H.d_prime.ne_zero
  simp at hsq
  exact H.d_prime.ne_zero hsq

/- English proof (translation)
Take `⟨x, -, rfl, h₂⟩` from `h`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, h₂]`. Conclude with `(Spec.map_comp _ _).symm`.
-/
theorem comp_s_eq_spMap_of_isOver {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
    {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {𝔐 : HodgeCpt Y S y} {z : Sp ℂ ⟶ 𝔐.X} {κ : c.F →+* ℂ}
    {p : Sp ℂ ⟶ Xo.X} (h : IsOver 𝔐 z κ p) :
    p ≫ Xo.s = spMap (κ.comp (IntermediateField.inclusion c.le).toRingHom) := by
  obtain ⟨x, -, rfl, h₂⟩ := h
  rw [Category.assoc, pullback.condition, ← Category.assoc, h₂]
  exact (Spec.map_comp _ _).symm

end GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
