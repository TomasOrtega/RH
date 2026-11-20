import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffZeroEqZeroIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TiltSeparatedCompleteEpsilonRootSubOne

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Decompl
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.DecomplFrob

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_frobW, coeff_inclW, coeff_inclW, WittVector.map_coeff, frobenius_def, map_pow]`.
-/
theorem frobW_inclW (a : Ainf l) :
    frobW l (inclW l a) = inclW l (WittVector.map (frobenius (OCb l) l) a) := by
  ext n
  rw [coeff_frobW, coeff_inclW, coeff_inclW, WittVector.map_coeff, frobenius_def, map_pow]

/- English proof (translation)
Use `⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]] WittVector.map (frobenius (OCb l) l) (crd (basisO LL) j a), ext_crd (basisO LL) fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[crd_φRW, crd_inclR, crd_inclR, crd_sum, frobW_inclW]`.
-/
theorem frob_inclR (LL : FinExt l) (a : RA LL) :
    ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a' := by
  refine ⟨∑ j, basisO LL j ⊗ₜ[ℤ_[l]]
    WittVector.map (frobenius (OCb l) l) (crd (basisO LL) j a), ext_crd (basisO LL) fun i => ?_⟩
  rw [crd_φRW, crd_inclR, crd_inclR, crd_sum, frobW_inclW]

/- English proof (translation)
Rewrite `hx`, the goal using `[nearPi_iff_crd]`. Introduce `i`. Take `⟨c, hc⟩` from `hx i`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le h`. Use `⟨(AI.εroot s - 1) ^ k * c ^ l, ?_⟩` and prove the remaining obligations.

Rewrite using `[crd_φRW, coeff_frobW, hc, ← map_pow, mul_pow, ← pow_mul, hk, pow_add, mul_assoc]`.
-/
theorem nearPi_frob {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s m n : ℕ)
    (h : n ≤ m * l) (x : RW LL) (hx : NearPi AI LL s m x) : NearPi AI LL s n (φRW LL x) := by
  rw [nearPi_iff_crd] at hx ⊢
  intro i
  obtain ⟨c, hc⟩ := hx i
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  refine ⟨(AI.εroot s - 1) ^ k * c ^ l, ?_⟩
  rw [crd_φRW, coeff_frobW, hc, ← map_pow, mul_pow, ← pow_mul, hk, pow_add, mul_assoc]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, 0, by simp⟩`.
-/
theorem near_self {A R : Type} [CommRing A] [CommRing R] (ι : A →+* R) (p : ℕ) (t : R) :
    Near ι p t 1 t := ⟨1, 0, by simp⟩

/- English proof (translation)
Introduce `h` and use `one_ne_zero ((GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 1 fun m => (h.pow m).dvd)`.
-/
theorem not_isUnit_root_sub_one {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) :
    ¬ IsUnit (AI.εroot s - 1) := fun h =>
  one_ne_zero ((GlobalTheory.TiltComplete.tilt_separated_complete l P AI s).1 1
    fun m => (h.pow m).dvd)

/- English proof (translation)
Assume the negation of the conclusion as `hz`. Establish `hu : IsUnit z`. Rewrite using `[PadicInt.isUnit_iff]`. Rewrite `hz` using `[← PadicInt.norm_lt_one_iff_dvd]`. Conclude with `le_antisymm z.2 (not_lt.1 hz)`.

Establish `h1 : z • (1 : WCb l) = inclW l (zlW l (OCb l) z)`. Rewrite using `[← Algebra.algebraMap_eq_smul_one]`. Conclude with `(map_zlW l (algebraMap (OCb l) (Cb l)) z).symm`. Rewrite `h` using `[h1, coeff_inclW, pow_one]`. Establish `h2` using `IsFractionRing.injective (OCb l) (Cb l) h`.

Establish `h3 : IsUnit ((zlW l (OCb l) z).coeff 0)` using `(hu.map (zlW l (OCb l))).map (WittVector.constantCoeff : Ainf l →+* OCb l)`. Rewrite `h3` using `[h2]`. Conclude with `not_isUnit_root_sub_one AI s (isUnit_of_mul_isUnit_left h3)`.
-/
theorem dvd_of_coeff {P : LocPrime l} (AI : LocAinf l P) (s : ℕ) (z : ℤ_[l]) (c : OCb l)
    (h : (z • (1 : WCb l)).coeff 0 = algebraMap (OCb l) (Cb l) ((AI.εroot s - 1) ^ 1 * c)) :
    (l : ℤ_[l]) ∣ z := by
  by_contra hz
  have hu : IsUnit z := by
    rw [PadicInt.isUnit_iff]
    rw [← PadicInt.norm_lt_one_iff_dvd] at hz
    exact le_antisymm z.2 (not_lt.1 hz)
  have h1 : z • (1 : WCb l) = inclW l (zlW l (OCb l) z) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (map_zlW l (algebraMap (OCb l) (Cb l)) z).symm
  rw [h1, coeff_inclW, pow_one] at h
  have h2 := IsFractionRing.injective (OCb l) (Cb l) h
  have h3 : IsUnit ((zlW l (OCb l) z).coeff 0) :=
    (hu.map (zlW l (OCb l))).map (WittVector.constantCoeff : Ainf l →+* OCb l)
  rw [h2] at h3
  exact not_isUnit_root_sub_one AI s (isUnit_of_mul_isUnit_left h3)

/- English proof (translation)
Rewrite `h` using `[nearPi_iff_crd]`. Establish `h1 : ∀ i, (l : ℤ_[l]) ∣ (basisO LL).repr o i` using `fun i => by`. Take `⟨c, hc⟩` from `h i`. Conclude with `dvd_of_coeff AI s _ c hc`. Use `choose d hd using h1`.

Use `⟨∑ i, d i • basisO LL i, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`. Use `((basisO LL).sum_repr o).symm.trans (Finset.sum_congr rfl fun i _ => ?_)` and prove the remaining obligations. Rewrite using `[hd, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]`.
-/
theorem const_dvd {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) (s : ℕ) (o : ↥(OL LL))
    (h : NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o)) :
    ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  rw [nearPi_iff_crd] at h
  have h1 : ∀ i, (l : ℤ_[l]) ∣ (basisO LL).repr o i := fun i => by
    obtain ⟨c, hc⟩ := h i
    exact dvd_of_coeff AI s _ c hc
  choose d hd using h1
  refine ⟨∑ i, d i • basisO LL i, ?_⟩
  rw [Finset.mul_sum]
  refine ((basisO LL).sum_repr o).symm.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [hd, mul_smul, Nat.cast_smul_eq_nsmul, nsmul_eq_mul]

/- English proof (translation)
Introduce `l hl P AI LL s`. Use `⟨frob_inclR LL, ?_, fun m x hx => ?_, const_dvd AI LL s⟩` and prove the remaining obligations. Conclude with `nearPi_frob AI LL s 1 2 (by rw [one_mul]; exact hl.out.two_le) _ (near_self _ _ _)`. Conclude with `nearPi_frob AI LL s m m (Nat.le_mul_of_pos_right m hl.out.pos) x hx`.
-/
theorem frobenius_and_constants : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (LL : FinExt l) (s : ℕ),
    (∀ a : RA LL, ∃ a' : RA LL, φRW LL (inclR LL a) = inclR LL a') ∧
    NearPi AI LL s 2 (φRW LL (piR AI LL s)) ∧
    (∀ (m : ℕ) (x : RW LL), NearPi AI LL s m x → NearPi AI LL s m (φRW LL x)) ∧
    ∀ o : ↥(OL LL), NearPi AI LL s 1 (algebraMap ↥(OL LL) (RW LL) o) →
      ∃ o' : ↥(OL LL), o = (l : ↥(OL LL)) * o' := by
  intro l hl P AI LL s
  refine ⟨frob_inclR LL, ?_, fun m x hx => ?_, const_dvd AI LL s⟩
  · exact nearPi_frob AI LL s 1 2 (by rw [one_mul]; exact hl.out.two_le) _ (near_self _ _ _)
  · exact nearPi_frob AI LL s m m (Nat.le_mul_of_pos_right m hl.out.pos) x hx

end GlobalTheory.DecomplFrob
