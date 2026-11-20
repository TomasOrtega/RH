import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMinimalPrimeComap
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

/- English proof (translation)
Set `` to `σ.toAlgebra`. Set `` to `MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)`. Establish `h : Algebra.IsPushout K (MvPolynomial ι K) L (MvPolynomial ι L)` using `inferInstance`. Conclude with `Module.Flat.isBaseChange K (MvPolynomial ι K) L (MvPolynomial ι L) h.out`.
-/
theorem MinimalPrimeComap.flat (K L : Type) [Field K] [Field L] (σ : K →+* L) (ι : Type) :
    let := σ.toAlgebra
    let := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
    Module.Flat (MvPolynomial ι K) (MvPolynomial ι L) := by
  let := σ.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have h : Algebra.IsPushout K (MvPolynomial ι K) L (MvPolynomial ι L) := inferInstance
  exact Module.Flat.isBaseChange K (MvPolynomial ι K) L (MvPolynomial ι L) h.out

/- English proof (translation)
Introduce `K L _ _ σ ι I hI P hP`. Set `` to `σ.toAlgebra`. Set `` to `MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)`. Use `MinimalPrimeComap.flat K L σ ι` as an intermediate fact. Establish `halg : algebraMap (MvPolynomial ι K) (MvPolynomial ι L) = MvPolynomial.map σ` using `rfl`.

Establish `: P.IsPrime` using `hP.1.1`. Establish `hle : I ≤ P.comap (MvPolynomial.map σ)` using `Ideal.map_le_iff_le_comap.mp hP.1.2`. Assume the negation of the conclusion as `hne`. Establish `hlt : I < P.under (MvPolynomial ι K)` using `lt_of_le_of_ne hle (fun h => hne h.symm)`. Establish `: (P.under (MvPolynomial ι K)).IsPrime` using `Ideal.IsPrime.under _ _`.

Establish `: P.LiesOver (P.under (MvPolynomial ι K))` using `⟨rfl⟩`. Take `⟨Q, hQP, hQ, hQI⟩` from `Ideal.exists_ideal_lt_liesOver_of_lt (p := I) P hlt`. Establish `hIQ : I.map (MvPolynomial.map σ) ≤ Q`. Rewrite using `[Ideal.map_le_iff_le_comap, ← halg, ← Ideal.under_def, ← hQI.over]`. Conclude with `(not_le_of_gt hQP) (hP.2 ⟨hQ, hIQ⟩ hQP.le)`.
-/
theorem MinimalPrimeComap.proof : MinimalPrimeComap.Statement := by
  intro K L _ _ σ ι I hI P hP
  let := σ.toAlgebra
  let := MvPolynomial.algebraMvPolynomial (σ := ι) (R := K) (S := L)
  have := MinimalPrimeComap.flat K L σ ι
  have halg : algebraMap (MvPolynomial ι K) (MvPolynomial ι L) = MvPolynomial.map σ := rfl
  have : P.IsPrime := hP.1.1
  have hle : I ≤ P.comap (MvPolynomial.map σ) := Ideal.map_le_iff_le_comap.mp hP.1.2
  by_contra hne
  have hlt : I < P.under (MvPolynomial ι K) := lt_of_le_of_ne hle (fun h => hne h.symm)
  have : (P.under (MvPolynomial ι K)).IsPrime := Ideal.IsPrime.under _ _
  have : P.LiesOver (P.under (MvPolynomial ι K)) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQI⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (p := I) P hlt
  have hIQ : I.map (MvPolynomial.map σ) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, ← halg, ← Ideal.under_def, ← hQI.over]
  exact (not_le_of_gt hQP) (hP.2 ⟨hQ, hIQ⟩ hQP.le)

end GroundTheory.Heights₂.Heights
