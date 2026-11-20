import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeckeMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentHomQuotientGaloisGroupScheme

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev

noncomputable section

namespace GlobalTheory.UPel.HT.EtLev.HeckeLev

variable {S : Scheme.{0}}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, pow_zero, one_comp]`. Consider the case `succ n ih => rw [pow_succ, pow_succ, mul_comp, ih]`.
-/
theorem pow_comp_hom {A B T : Over S} [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (x : T ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_comp]
  | succ n ih => rw [pow_succ, pow_succ, mul_comp, ih]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero, Hom.one_def]`. Use `infer_instance`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))`.
-/
theorem isMonHom_idPow (A : Over S) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n : A ⟶ A) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 A) ^ n) (𝟙 A) ≫ μ[A]))

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Establish `h` using `act.add 0 0`. Rewrite `h` using `[add_zero]`. Rewrite using `[Nat.cast_zero, pow_zero]`.

Conclude with `mul_left_cancel (a := act.act 0) (by rw [_root_.mul_one]; exact h.symm)`. Consider the case `succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]`.
-/
theorem act_natCast {A : Over S} [GrpObj A] (act : OActN D.O A) (n : ℕ) :
    act.act (n : D.O) = (𝟙 A) ^ n := by
  induction n with
  | zero =>
    have h := act.add 0 0
    rw [add_zero] at h
    rw [Nat.cast_zero, pow_zero]
    exact mul_left_cancel (a := act.act 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ n ih => rw [Nat.cast_succ, act.add, ih, act.one, pow_succ]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [zero_smul, h0, pow_zero]`. Consider the case `succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]`.
-/
theorem map_nsmul_pow {A : Over S} [GrpObj A] (f : D.La → (𝟙_ (Over S) ⟶ A))
    (hadd : ∀ x y, f (x + y) = f x * f y) (h0 : f 0 = 1) (n : ℕ) (y : D.La) : f (n • y) = f y ^ n := by
  induction n with
  | zero => rw [zero_smul, h0, pow_zero]
  | succ n ih => rw [succ_nsmul, hadd, ih, pow_succ]

end GlobalTheory.UPel.HT.EtLev.HeckeLev
