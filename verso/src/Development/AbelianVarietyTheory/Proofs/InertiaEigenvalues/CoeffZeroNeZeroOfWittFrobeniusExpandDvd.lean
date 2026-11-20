import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisPrescribedUnramifiedKummer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvdSubOfDvdSubX
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory

/- English proof (translation)
Take `⟨P0, hP0, hnd⟩` from `Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0`. Generalize the expression as in `Polynomial.rootMultiplicity 0 P = k at hP0`. Simplify using `only [map_zero, sub_zero] at hP0 hnd`. Introduce `h0`. Establish `hk : k ≠ 0`.

Introduce and unpack `rfl`. Apply `hnd` to reduce the goal to its premises. Rewrite using `[Polynomial.X_dvd_iff]`. Simplify `h0` using `[hP0]`. Establish `h1 : (Polynomial.X : Polynomial R) ^ k * Polynomial.X ∣ Polynomial.expand R l (P.map σ)`.

Rewrite using `[hP0, Polynomial.map_mul, map_mul, Polynomial.map_pow, Polynomial.map_X, map_pow, Polynomial.expand_X, ← pow_mul, ← pow_succ]`. Use `Dvd.dvd.mul_right (pow_dvd_pow _ ?_) _` and prove the remaining obligations. Establish `: 1 ≤ k` using `Nat.one_le_iff_ne_zero.mpr hk`. Use the polynomial consequences of the given equalities and inequalities. Establish `h2` using `h1.trans h`.

Establish `h3 : E ^ M * P = Polynomial.X ^ k * (E ^ M * P0)` using `by rw [hP0]; ring`. Rewrite `h2` using `[h3, mul_dvd_mul_iff_left (pow_ne_zero _ Polynomial.X_ne_zero)]`. Break down `Polynomial.prime_X.dvd_or_dvd h2 with h4 | h4` into its components or cases. Conclude with `hE (Polynomial.X_dvd_iff.mp (Polynomial.prime_X.dvd_of_dvd_pow h4))`. Conclude with `hnd h4`.
-/
theorem coeff_zero_ne_zero_of_expand_map_dvd {R : Type*} [CommRing R] [IsDomain R] (l : ℕ) (hl : 2 ≤ l)
    (σ : R →+* R) (P E : Polynomial R) (M : ℕ) (hP : P ≠ 0) (hE : E.coeff 0 ≠ 0)
    (h : Polynomial.expand R l (P.map σ) ∣ E ^ M * P) : P.coeff 0 ≠ 0 := by
  obtain ⟨P0, hP0, hnd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP 0
  generalize Polynomial.rootMultiplicity 0 P = k at hP0
  simp only [map_zero, sub_zero] at hP0 hnd
  intro h0
  have hk : k ≠ 0 := by
    rintro rfl
    apply hnd
    rw [Polynomial.X_dvd_iff]
    simpa [hP0] using h0
  have h1 : (Polynomial.X : Polynomial R) ^ k * Polynomial.X ∣ Polynomial.expand R l (P.map σ) := by
    rw [hP0, Polynomial.map_mul, map_mul, Polynomial.map_pow, Polynomial.map_X, map_pow,
      Polynomial.expand_X, ← pow_mul, ← pow_succ]
    refine Dvd.dvd.mul_right (pow_dvd_pow _ ?_) _
    have : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk
    nlinarith
  have h2 := h1.trans h
  have h3 : E ^ M * P = Polynomial.X ^ k * (E ^ M * P0) := by rw [hP0]; ring
  rw [h3, mul_dvd_mul_iff_left (pow_ne_zero _ Polynomial.X_ne_zero)] at h2
  rcases Polynomial.prime_X.dvd_or_dvd h2 with h4 | h4
  · exact hE (Polynomial.X_dvd_iff.mp (Polynomial.prime_X.dvd_of_dvd_pow h4))
  · exact hnd h4

/- English proof (translation)
Introduce `l hl a _ P E M hP hE h`. Conclude with `coeff_zero_ne_zero_of_expand_map_dvd l hl.out.two_le _ P E M hP.ne_zero hE h`.
-/
theorem coeff_zero_ne_zero_of_frobenius_dvd_pow_mul :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (P E : Polynomial (Wq l a)) (M : ℕ), P.Monic → E.coeff 0 ≠ 0 →
    Polynomial.expand (Wq l a) l (P.map (sigma l a : Wq l a →+* Wq l a)) ∣ E ^ M * P → P.coeff 0 ≠ 0 := by
  intro l hl a _ P E M hP hE h
  exact coeff_zero_ne_zero_of_expand_map_dvd l hl.out.two_le _ P E M hP.ne_zero hE h

end GlobalTheory
