import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.PLatticeSaturatedAndCofinite

open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

/- English proof (translation)
Introduce `p _ D X g hg`. Use `haveI := D.finLa`. Establish `hnd : X.B.Nondegenerate` using `(LinearMap.IsRefl.nondegenerate_iff_separatingLeft (LinearMap.IsAlt.isRefl X.alt)).mpr X.nondeg`. Use `set w0 := (X.B.toDual hnd).symm g with hw0`. Establish `hB : ∀ u, X.B w0 u = g u`.

Introduce `u`. Rewrite using `[← LinearMap.BilinForm.toDual_def hnd, hw0, LinearEquiv.apply_symm_apply]`. Establish `hw : ∀ u, X.s * X.B (X.s⁻¹ • w0) u = g u`. Introduce `u`. Rewrite using `[map_smul, LinearMap.smul_apply, hB, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ X.s_pos.ne', one_mul]`.

Use `⟨X.s⁻¹ • w0, ?_, hw⟩` and prove the remaining obligations. Rewrite using `[X.perf]`. Introduce `u hu`. Rewrite using `[hw]`. Take `⟨t, ht0, htp, htm⟩` from `DenEnd.exists_coprime_nsmul_mem D (X.r u)`.

Establish `hlat : t • u ∈ X.lat` using `⟨X.M.nsmul_mem hu t, by rw [map_nsmul]; exact htm⟩`. Take `⟨z, hz⟩` from `hg _ hlat`. Rewrite `hz` using `[map_nsmul, nsmul_eq_mul]`. Establish `ht : (t : ℚ) ≠ 0` using `by exact_mod_cast ht0.ne'`. Establish `hq : g u = (z : ℚ) / (t : ℚ)`.

Rewrite using `[eq_div_iff ht, mul_comm, hz]`. Establish `hd` using `Rat.den_dvd z t`. Rewrite `hd` using `[Rat.divInt_eq_div]`. Move the coercions through the operations in `at hd`. Rewrite using `[hq]`.

Conclude with `Nat.Coprime.coprime_dvd_left (Int.natCast_dvd_natCast.mp hd) htp`.
-/
theorem UpperTheory.exists_dual_vector_of_integral_functional :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (g : VQ D →ₗ[ℚ] ℚ), (∀ u ∈ X.lat, ∃ z : ℤ, g u = z) → ∃ w ∈ X.M, ∀ u, X.s * X.B w u = g u := by
  intro p _ D X g hg
  haveI := D.finLa
  have hnd : X.B.Nondegenerate :=
    (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (LinearMap.IsAlt.isRefl X.alt)).mpr X.nondeg
  set w0 := (X.B.toDual hnd).symm g with hw0
  have hB : ∀ u, X.B w0 u = g u := by
    intro u
    rw [← LinearMap.BilinForm.toDual_def hnd, hw0, LinearEquiv.apply_symm_apply]
  have hw : ∀ u, X.s * X.B (X.s⁻¹ • w0) u = g u := by
    intro u
    rw [map_smul, LinearMap.smul_apply, hB, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ X.s_pos.ne', one_mul]
  refine ⟨X.s⁻¹ • w0, ?_, hw⟩
  rw [X.perf]
  intro u hu
  rw [hw]
  obtain ⟨t, ht0, htp, htm⟩ := DenEnd.exists_coprime_nsmul_mem D (X.r u)
  have hlat : t • u ∈ X.lat := ⟨X.M.nsmul_mem hu t, by rw [map_nsmul]; exact htm⟩
  obtain ⟨z, hz⟩ := hg _ hlat
  rw [map_nsmul, nsmul_eq_mul] at hz
  have ht : (t : ℚ) ≠ 0 := by exact_mod_cast ht0.ne'
  have hq : g u = (z : ℚ) / (t : ℚ) := by
    rw [eq_div_iff ht, mul_comm, hz]
  have hd := Rat.den_dvd z t
  rw [Rat.divInt_eq_div] at hd
  push_cast at hd
  rw [hq]
  exact Nat.Coprime.coprime_dvd_left (Int.natCast_dvd_natCast.mp hd) htp
