import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComplexMinimalPrimesContract
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.algebraMvPolynomial

/- English proof (translation)
The claim follows from `Module.Flat.isBaseChange ℤ (MvPolynomial σ ℤ) ℂ (MvPolynomial σ ℂ) (Algebra.IsPushout.out (R := ℤ) (S := MvPolynomial σ ℤ) (R' := ℂ) (S' := MvPolynomial σ ℂ))`.
-/
theorem mvPolynomial_int_complex_flat (σ : Type) :
    Module.Flat (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℤ (MvPolynomial σ ℤ) ℂ (MvPolynomial σ ℂ)
    (Algebra.IsPushout.out (R := ℤ) (S := MvPolynomial σ ℤ) (R' := ℂ) (S' := MvPolynomial σ ℂ))

/- English proof (translation)
Rewrite using `[MvPolynomial.algebraMap_def]`. Use `congr 1`.
-/
theorem algebraMap_mvPolynomial_int_complex (σ : Type) :
    algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℂ) = MvPolynomial.map (Int.castRingHom ℂ) := by
  rw [MvPolynomial.algebraMap_def]
  congr 1

/- English proof (translation)
Introduce `σ _ P hP Q hQ`. Use `hP` as an intermediate fact. Establish `hflat` using `mvPolynomial_int_complex_flat σ`. Establish `hAlg` using `algebraMap_mvPolynomial_int_complex σ`. Establish `: Q.IsPrime` using `hQ.1.1`.

Establish `hPQ : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q` using `hQ.1.2`. Establish `hle : P ≤ Q.comap (MvPolynomial.map (Int.castRingHom ℂ))` using `Ideal.map_le_iff_le_comap.mp hPQ`. Establish `: (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))).IsPrime` using `Ideal.comap_isPrime _ Q`. Establish `: Q.LiesOver (Q.comap (MvPolynomial.map (Int.castRingHom ℂ)))` using `⟨by rw [Ideal.under, Ideal.comap, hAlg]; rfl⟩`. Take `⟨Q', hQ'Q, hQ'prime, hQ'over⟩` from `Ideal.exists_ideal_le_liesOver_of_le (R := MvPolynomial σ ℤ) (p := P) (q := Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) Q hle`.

Establish `hQ'P : Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P`. Use `hQ'over.over` as an intermediate fact. Rewrite `this` using `[Ideal.under, hAlg]`. Conclude with `this.symm`. Establish `hmapQ' : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q'` using `Ideal.map_le_iff_le_comap.mpr hQ'P.ge`.

Establish `hQQ' : Q ≤ Q'` using `hQ.2 ⟨hQ'prime, hmapQ'⟩ hQ'Q`. Rewrite using `[← le_antisymm hQ'Q hQQ']`. Conclude with `hQ'P`.
-/
theorem ComplexMinimalPrimesContract.proof : ComplexMinimalPrimesContract.Statement := by
  intro σ _ P hP Q hQ
  have := hP
  have hflat := mvPolynomial_int_complex_flat σ
  have hAlg := algebraMap_mvPolynomial_int_complex σ
  have : Q.IsPrime := hQ.1.1
  have hPQ : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q := hQ.1.2
  have hle : P ≤ Q.comap (MvPolynomial.map (Int.castRingHom ℂ)) :=
    Ideal.map_le_iff_le_comap.mp hPQ
  have : (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))).IsPrime := Ideal.comap_isPrime _ Q
  have : Q.LiesOver (Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) :=
    ⟨by rw [Ideal.under, Ideal.comap, hAlg]; rfl⟩
  obtain ⟨Q', hQ'Q, hQ'prime, hQ'over⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (R := MvPolynomial σ ℤ) (p := P)
      (q := Q.comap (MvPolynomial.map (Int.castRingHom ℂ))) Q hle
  have hQ'P : Q'.comap (MvPolynomial.map (Int.castRingHom ℂ)) = P := by
    have := hQ'over.over
    rw [Ideal.under, hAlg] at this
    exact this.symm
  have hmapQ' : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ Q' :=
    Ideal.map_le_iff_le_comap.mpr hQ'P.ge
  have hQQ' : Q ≤ Q' := hQ.2 ⟨hQ'prime, hmapQ'⟩ hQ'Q
  rw [← le_antisymm hQ'Q hQQ']
  exact hQ'P

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
