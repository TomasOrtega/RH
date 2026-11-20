import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.AuxiliaryInertOddPrime
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKDef GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL
open scoped TensorProduct

/- English proof (translation)
Introduce `hB E _ _ _ hev A n p _ S hn`. Take `⟨hga, -, hc⟩` from `hB E A n p S`. Establish `hmul : Module.finrank ℚ (maximalRealSubfield E) * Module.finrank (maximalRealSubfield E) E = Module.finrank ℚ E` using `Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E`. Establish `h2 : Module.finrank (maximalRealSubfield E) E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two _ _`. Establish `hpos : 0 < Module.finrank ℚ (maximalRealSubfield E)` using `Module.finrank_pos`.

Establish `hlt : 2 < Module.finrank ℚ E`. Take `⟨k, hk⟩` from `hev`. Rewrite using `[← hmul, h2]`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨rfl, rfl, hga, hn, (hc hlt).2⟩`.
-/
theorem UpperTheory.Gal.G1.pScOf :
    SetupBasic → ScOf := by
  intro hB E _ _ _ hev A n p _ S hn
  obtain ⟨hga, -, hc⟩ := hB E A n p S
  have hmul : Module.finrank ℚ (maximalRealSubfield E) * Module.finrank (maximalRealSubfield E) E =
      Module.finrank ℚ E := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  have h2 : Module.finrank (maximalRealSubfield E) E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hpos : 0 < Module.finrank ℚ (maximalRealSubfield E) := Module.finrank_pos
  have hlt : 2 < Module.finrank ℚ E := by
    obtain ⟨k, hk⟩ := hev
    rw [← hmul, h2]
    omega
  exact ⟨rfl, rfl, hga, hn, (hc hlt).2⟩
