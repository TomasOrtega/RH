import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChart

namespace ReciprocityTheory.AnForm.R
open MvPolynomial
noncomputable section

variable {n : ℕ}

def ptQ (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) : Ideal (MvPolynomial (Fin n) ℂ ⧸ K) :=
  (ptIdeal p).map (Ideal.Quotient.mk K)

/- English proof (translation)
Conclude with `Ideal.mem_quotient_iff_mem hK`.
-/
theorem mk_mem_ptQ {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ} (hK : K ≤ ptIdeal p)
    (f : MvPolynomial (Fin n) ℂ) : Ideal.Quotient.mk K f ∈ ptQ K p ↔ f ∈ ptIdeal p := by
  exact Ideal.mem_quotient_iff_mem hK

/- English proof (translation)
Use `haveI : (ptIdeal p).IsPrime := RingHom.ker_isPrime _`. Conclude with `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hK)`.
-/
theorem ptQ_isPrime {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ} (hK : K ≤ ptIdeal p) :
    (ptQ K p).IsPrime := by
  haveI : (ptIdeal p).IsPrime := RingHom.ker_isPrime _
  exact Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hK)

/- English proof (translation)
Rewrite using `[← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]`.
-/
theorem algebraMap_quot_mk (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (f : MvPolynomial (Fin n) ℂ) :
    algebraMap (MvPolynomial (Fin n) ℂ ⧸ K) (locRing K p) (Ideal.Quotient.mk K f) =
      algebraMap _ (locRing K p) f := by
  rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Use `letI := ptQ_isPrime hK`. Establish `hM : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ K) (ptIdeal p).primeCompl = (ptQ K p).primeCompl`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨f, hf, rfl⟩`.

Rewrite using `[Ideal.mem_primeCompl_iff, Ideal.Quotient.algebraMap_eq, mk_mem_ptQ hK]`. Conclude with `hf`. Introduce `hx`. Take `⟨f, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite `hx` using `[Ideal.mem_primeCompl_iff, mk_mem_ptQ hK]`.

Conclude with `⟨f, hx, rfl⟩`. Establish `h` using `IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap (ptIdeal p).primeCompl (locPt p) K`. Rewrite `h` using `[hM]`. Conclude with `h`.
-/
theorem isLocalization_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) :
    letI := ptQ_isPrime hK; IsLocalization.AtPrime (locRing K p) (ptQ K p) := by
  letI := ptQ_isPrime hK
  have hM : Algebra.algebraMapSubmonoid (MvPolynomial (Fin n) ℂ ⧸ K) (ptIdeal p).primeCompl =
      (ptQ K p).primeCompl := by
    ext x
    constructor
    · rintro ⟨f, hf, rfl⟩
      rw [Ideal.mem_primeCompl_iff, Ideal.Quotient.algebraMap_eq, mk_mem_ptQ hK]
      exact hf
    · intro hx
      obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [Ideal.mem_primeCompl_iff, mk_mem_ptQ hK] at hx
      exact ⟨f, hx, rfl⟩
  have h := IsLocalization.instQuotientIdealAlgebraMapSubmonoidMapRingHomAlgebraMap
    (ptIdeal p).primeCompl (locPt p) K
  rw [hM] at h
  exact h

/- English proof (translation)
Use `letI := ptQ_isPrime hK`. Use `haveI := isLocalization_locRing hK`. Conclude with `IsLocalization.AtPrime.isLocalRing (locRing K p) (ptQ K p)`.
-/
theorem isLocalRing_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) : IsLocalRing (locRing K p) := by
  letI := ptQ_isPrime hK
  haveI := isLocalization_locRing hK
  exact IsLocalization.AtPrime.isLocalRing (locRing K p) (ptQ K p)

/- English proof (translation)
Use `letI := ptQ_isPrime hK`. Use `haveI := isLocalization_locRing hK`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (ptQ K p) (locRing K p), ptQ, Ideal.map_map]`. Use `congr 1`.
-/
theorem maximalIdeal_locRing {K : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (hK : K ≤ ptIdeal p) [IsLocalRing (locRing K p)] :
    IsLocalRing.maximalIdeal (locRing K p) = (ptIdeal p).map (algebraMap _ (locRing K p)) := by
  letI := ptQ_isPrime hK
  haveI := isLocalization_locRing hK
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (ptQ K p) (locRing K p), ptQ, Ideal.map_map]
  congr 1

/- English proof (translation)
Simplify using `[ptIdeal, SetLike.le_def, RingHom.mem_ker]`.
-/
theorem le_ptIdeal_iff' (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ) :
    K ≤ ptIdeal p ↔ ∀ h ∈ K, eval p h = 0 := by
  simp [ptIdeal, SetLike.le_def, RingHom.mem_ker]

end
end ReciprocityTheory.AnForm.R
