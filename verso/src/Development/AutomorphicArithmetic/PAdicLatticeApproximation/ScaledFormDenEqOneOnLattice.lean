import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsPPowMulIntOfIsIntAfAlgebraMap

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

/- English proof (translation)
Introduce `p _ D X u w hu hw`. Establish `hu' : u ∈ X.M ∧ X.r u ∈ LaHat D`. Unfold `UpperTheory.Gal.W2.Wit.Sys.lat at hu`. Simplify `hu` using `only [AddSubgroup.mem_mk, AddSubgroup.mem_comap, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]`. Establish `hw' : w ∈ X.M ∧ X.r w ∈ LaHat D`.

Unfold `UpperTheory.Gal.W2.Wit.Sys.lat at hw`. Simplify `hw` using `only [AddSubgroup.mem_mk, AddSubgroup.mem_comap, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]`. Establish `hint : IsIntAf (algebraMap ℚ (AfP p) (X.s * X.B u w))`. Rewrite using `[X.form u w]`. Conclude with `AdelicSim.isInt_mul X.ε_int (AdelicSim.formInt D hu'.2 hw'.2)`.

Establish `hcop : (X.s * X.B u w).den.Coprime p` using `(X.perf u).mp hu'.1 w hw'.1`. Take `⟨r, z, hz⟩` from `UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap p _ hint`. Use `set q : ℚ := X.s * X.B u w with hq`. Establish `e : ((p : ℤ) ^ r * q.num : ℤ) = z * q.den`. Establish `h : ((p : ℚ) ^ r * q.num : ℚ) = z * q.den`.

Rewrite using `[← hz, mul_assoc, Rat.mul_den_eq_num]`. Conclude with `h` after adjusting the coercions. Establish `hdvd : (q.den : ℤ) ∣ (p : ℤ) ^ r * q.num` using `⟨z, by rw [e]; ring⟩`. Rewrite `hdvd` using `[Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]`. Establish `h2 : q.den ∣ p ^ r` using `(Nat.Coprime.symm q.reduced).dvd_of_dvd_mul_right hdvd`.

Conclude with `Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right r hcop) h2`.
-/
theorem UpperTheory.scaled_form_den_eq_one_on_lattice :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (u w : VQ D), u ∈ X.lat → w ∈ X.lat → (X.s * X.B u w).den = 1 := by
  intro p _ D X u w hu hw
  have hu' : u ∈ X.M ∧ X.r u ∈ LaHat D := by
    unfold UpperTheory.Gal.W2.Wit.Sys.lat at hu
    simpa only [AddSubgroup.mem_mk, AddSubgroup.mem_comap, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] using hu
  have hw' : w ∈ X.M ∧ X.r w ∈ LaHat D := by
    unfold UpperTheory.Gal.W2.Wit.Sys.lat at hw
    simpa only [AddSubgroup.mem_mk, AddSubgroup.mem_comap, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq] using hw
  have hint : IsIntAf (algebraMap ℚ (AfP p) (X.s * X.B u w)) := by
    rw [X.form u w]
    exact AdelicSim.isInt_mul X.ε_int (AdelicSim.formInt D hu'.2 hw'.2)
  have hcop : (X.s * X.B u w).den.Coprime p := (X.perf u).mp hu'.1 w hw'.1
  obtain ⟨r, z, hz⟩ := UpperTheory.exists_p_pow_mul_int_of_isIntAf_algebraMap p _ hint
  set q : ℚ := X.s * X.B u w with hq
  have e : ((p : ℤ) ^ r * q.num : ℤ) = z * q.den := by
    have h : ((p : ℚ) ^ r * q.num : ℚ) = z * q.den := by
      rw [← hz, mul_assoc, Rat.mul_den_eq_num]
    exact_mod_cast h
  have hdvd : (q.den : ℤ) ∣ (p : ℤ) ^ r * q.num := ⟨z, by rw [e]; ring⟩
  rw [Int.natCast_dvd, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast] at hdvd
  have h2 : q.den ∣ p ^ r := (Nat.Coprime.symm q.reduced).dvd_of_dvd_mul_right hdvd
  exact Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right r hcop) h2
