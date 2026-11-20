import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatActApply

noncomputable section

namespace GlobalTheory.UPel.HT.LieLin.RankIdeal

open NumberField

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

/- English proof (translation)
Establish `h` using `b.ρ_root`. Use `push_cast`. Take the linear combination `4 * h`.
-/
theorem sq_two_mul_rho_sub_tr (b : Base D R) :
    (2 * b.ρ - (D.tr : R)) ^ 2 = ((D.tr ^ 2 - 4 * D.nm : ℤ) : R) := by
  have h := b.ρ_root
  push_cast
  linear_combination 4 * h

/- English proof (translation)
Establish `hp : (p).Prime` using `Fact.out`. Use `set d : ℤ := D.tr ^ 2 - 4 * D.nm with hd`. Establish `hc : d.natAbs.Coprime p`. Use `Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => D.disc_p ?_)` and prove the remaining obligations. Conclude with `Int.natCast_dvd.2 h`.

Establish `hu` using `b.unit _ hc`. Establish `hdu : IsUnit ((d : ℤ) : R)`. Break down `Int.natAbs_eq d with h | h` into its components or cases. Rewrite using `[h, Int.cast_natCast]`. Conclude with `hu`.

Rewrite using `[h, Int.cast_neg, Int.cast_natCast]`. Conclude with `hu.neg`. Rewrite `hdu` using `[← sq_two_mul_rho_sub_tr]`. Conclude with `(isUnit_pow_iff two_ne_zero).1 hdu`.
-/
theorem isUnit_two_mul_rho_sub_tr (b : Base D R) : IsUnit (2 * b.ρ - (D.tr : R)) := by
  have hp : (p).Prime := Fact.out
  set d : ℤ := D.tr ^ 2 - 4 * D.nm with hd
  have hc : d.natAbs.Coprime p := by
    refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => D.disc_p ?_)
    exact Int.natCast_dvd.2 h
  have hu := b.unit _ hc
  have hdu : IsUnit ((d : ℤ) : R) := by
    rcases Int.natAbs_eq d with h | h
    · rw [h, Int.cast_natCast]; exact hu
    · rw [h, Int.cast_neg, Int.cast_natCast]; exact hu.neg
  rw [← sq_two_mul_rho_sub_tr] at hdu
  exact (isUnit_pow_iff two_ne_zero).1 hdu

def uInv (b : Base D R) : R := ↑(isUnit_two_mul_rho_sub_tr b).unit⁻¹

/- English proof (translation)
The claim follows from `(isUnit_two_mul_rho_sub_tr b).val_inv_mul`.
-/
theorem uInv_mul (b : Base D R) : uInv b * (2 * b.ρ - (D.tr : R)) = 1 :=
  (isUnit_two_mul_rho_sub_tr b).val_inv_mul

def comaxC (b : Base D R) (i j : Fin D.a) : 𝓞 D.F →₀ R :=
  if h : i ≠ j then
    Classical.choose (Finsupp.mem_span_range_iff_exists_finsupp.1
      ((b.comax i j h).symm ▸ Submodule.mem_top :
        (1 : R) ∈ Ideal.span (Set.range fun x => b.t i x - b.t j x)))
  else 0

/- English proof (translation)
Unfold `comaxC`. Rewrite using `[dif_pos h]`. Conclude with `Classical.choose_spec (Finsupp.mem_span_range_iff_exists_finsupp.1 ((b.comax i j h).symm ▸ Submodule.mem_top : (1 : R) ∈ Ideal.span (Set.range fun x => b.t i x - b.t j x)))`.
-/
theorem comaxC_spec (b : Base D R) {i j : Fin D.a} (h : i ≠ j) :
    ((comaxC b i j).sum fun x r => r * (b.t i x - b.t j x)) = 1 := by
  unfold comaxC
  rw [dif_pos h]
  exact Classical.choose_spec (Finsupp.mem_span_range_iff_exists_finsupp.1
      ((b.comax i j h).symm ▸ Submodule.mem_top :
        (1 : R) ∈ Ideal.span (Set.range fun x => b.t i x - b.t j x)))

variable {B : Type} [CommRing B] {n : ℕ}

def alphaMat (b : Base D R) (βB : R →+* B) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (i j : Fin D.a) :
    Matrix (Fin n) (Fin n) B :=
  (comaxC b i j).sum fun x r =>
    algebraMap B (Matrix (Fin n) (Fin n) B) (βB r) * (M x - algebraMap B (Matrix (Fin n) (Fin n) B) (βB (b.t j x)))

def projMat (b : Base D R) (βB : R →+* B) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (i : Fin D.a) :
    Matrix (Fin n) (Fin n) B :=
  (List.ofFn fun j => if j = i then 1 else alphaMat b βB M i j).prod *
    (algebraMap B (Matrix (Fin n) (Fin n) B) (βB (uInv b)) *
      (M D.ω - algebraMap B (Matrix (Fin n) (Fin n) B) (βB ((D.tr : R) - b.ρ))))

end GlobalTheory.UPel.HT.LieLin.RankIdeal
