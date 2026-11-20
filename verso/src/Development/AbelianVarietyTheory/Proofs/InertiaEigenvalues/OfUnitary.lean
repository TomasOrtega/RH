import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOneUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulIsUnitary
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspSubZeroVEqTop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
open GlobalTheory.Published

noncomputable section

open NumberField Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.CuspMultOne

/- English proof (translation)
Introduce `h E _ _ _ a π π' e`. Break down `Nat.eq_zero_or_pos a with rfl | ha` into its components or cases. Conclude with `GlobalTheory.cuspSub_zero_V_eq E π π'`. Take `⟨ω, hω⟩` from `GlobalTheory.CuspRep.Central.exists_hasCentral E a π`. Establish `hiso : CuspSub.Iso π π'` using `Quotient.exact (s := CuspSub.setoid E a) e`.

Establish `hω'` using `hiso.hasCentral hω`. Take `⟨ν, hν⟩` from `GlobalTheory.UnitaryTwist.exists_pow_mul_isUnitary E ω a ha`. Establish `hu` using `(hω.twist ν).isUnitary_iff.2 hν`. Establish `hu'` using `(hω'.twist ν).isUnitary_iff.2 hν`. Establish `he : CG.mk (π.twist ν) = CG.mk (π'.twist ν)` using `Quotient.sound (s := CuspSub.setoid E a) (hiso.twist ν)`.

Establish `ht : π.twist ν = π'.twist ν` using `CuspSub.ext (h E a ha _ _ hu hu' he)`. Establish `h2 : π.twist (ν * ν⁻¹) = π'.twist (ν * ν⁻¹)`. Rewrite using `[CuspSub.twist_mul, CuspSub.twist_mul, ht]`. Rewrite `h2` using `[mul_inv_cancel, CuspSub.twist_one, CuspSub.twist_one]`. Rewrite using `[h2]`.
-/
theorem of_unitary : CuspidalMultiplicityOneUnitary → CuspidalMultiplicityOne := by
  intro h E _ _ _ a π π' e
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact GlobalTheory.cuspSub_zero_V_eq E π π'
  obtain ⟨ω, hω⟩ := GlobalTheory.CuspRep.Central.exists_hasCentral E a π
  have hiso : CuspSub.Iso π π' := Quotient.exact (s := CuspSub.setoid E a) e
  have hω' := hiso.hasCentral hω
  obtain ⟨ν, hν⟩ := GlobalTheory.UnitaryTwist.exists_pow_mul_isUnitary E ω a ha
  have hu := (hω.twist ν).isUnitary_iff.2 hν
  have hu' := (hω'.twist ν).isUnitary_iff.2 hν
  have he : CG.mk (π.twist ν) = CG.mk (π'.twist ν) :=
    Quotient.sound (s := CuspSub.setoid E a) (hiso.twist ν)
  have ht : π.twist ν = π'.twist ν := CuspSub.ext (h E a ha _ _ hu hu' he)
  have h2 : π.twist (ν * ν⁻¹) = π'.twist (ν * ν⁻¹) := by
    rw [CuspSub.twist_mul, CuspSub.twist_mul, ht]
  rw [mul_inv_cancel, CuspSub.twist_one, CuspSub.twist_one] at h2
  rw [h2]

end GlobalTheory.CuspMultOne

end
