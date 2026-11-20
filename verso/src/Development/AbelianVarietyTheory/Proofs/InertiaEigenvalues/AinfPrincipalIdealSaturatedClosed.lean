import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfSat

section Coeff

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

/- English proof (translation)
Proceed by induction on `r with`. Consider the case `zero => simp`. Consider the case `succ r ih`. Establish `h : (p : WittVector p R) ^ (r + 1) * w = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ r * w))`. Rewrite using `[WittVector.verschiebung_frobenius]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h, show i + (r + 1) = (i + r).succ by omega, WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP, ih, ← pow_mul, pow_succ]`.
-/
theorem coeff_pow_mul_add (r : ℕ) (w : WittVector p R) (i : ℕ) :
    (((p : WittVector p R) ^ r * w).coeff (i + r)) = (w.coeff i) ^ (p ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : (p : WittVector p R) ^ (r + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ r * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h, show i + (r + 1) = (i + r).succ by omega, WittVector.verschiebung_coeff_succ,
      WittVector.coeff_frobenius_charP, ih, ← pow_mul, pow_succ]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => intro j hj`. Use linear arithmetic over natural numbers and integers. Consider the case `succ n ih`. Introduce `j hj`.

Establish `h : (p : WittVector p R) ^ (n + 1) * w = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ n * w))`. Rewrite using `[WittVector.verschiebung_frobenius]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h]`. Consider the cases of `j with`.

Consider the case `zero => exact WittVector.verschiebung_coeff_zero _`. Consider the case `succ j`. Rewrite using `[WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP, ih j (by omega), zero_pow hp.out.ne_zero]`.
-/
theorem coeff_pow_mul_lt (n : ℕ) (w : WittVector p R) :
    ∀ j, j < n → ((p : WittVector p R) ^ n * w).coeff j = 0 := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have h : (p : WittVector p R) ^ (n + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ n * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ j =>
      rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP, ih j (by omega),
        zero_pow hp.out.ne_zero]

/- English proof (translation)
Take `⟨w, hw⟩` from `h`. Establish `hz : WittVector.truncate n (u - v) = 0`. Use extensionality with `k`. Rewrite using `[WittVector.coeff_truncate, hw, coeff_pow_mul_lt n w k k.2]`. Simplify using the standard rewrite rules.

Establish `ht : WittVector.truncate n u = WittVector.truncate n v`. Rewrite `hz` using `[map_sub, sub_eq_zero]`. Conclude with `hz`. Use `congrArg (TruncatedWittVector.coeff (⟨j, hj⟩ : Fin n)) ht` as an intermediate fact. Simplify `this` using `[WittVector.coeff_truncate]`.
-/
theorem coeff_eq_of_dvd {n : ℕ} {u v : WittVector p R} (h : (p : WittVector p R) ^ n ∣ u - v)
    (j : ℕ) (hj : j < n) : u.coeff j = v.coeff j := by
  obtain ⟨w, hw⟩ := h
  have hz : WittVector.truncate n (u - v) = 0 := by
    ext k
    rw [WittVector.coeff_truncate, hw, coeff_pow_mul_lt n w k k.2]
    simp
  have ht : WittVector.truncate n u = WittVector.truncate n v := by
    rw [map_sub, sub_eq_zero] at hz; exact hz
  have := congrArg (TruncatedWittVector.coeff (⟨j, hj⟩ : Fin n)) ht
  simpa [WittVector.coeff_truncate] using this

end Coeff

variable (l : ℕ) [Fact l.Prime]

/- English proof (translation)
Use `⟨(iterateFrobeniusEquiv (OCb l) l r).symm b, ?_⟩` and prove the remaining obligations. Apply `iterateFrobenius_inj (Cb l) l r` to reduce the goal to its premises. Rewrite using `[iterateFrobenius_def, iterateFrobenius_def, h, ← map_pow]`. Use `congr 1`. Use `(iterateFrobeniusEquiv (OCb l) l r).apply_symm_apply b` as an intermediate fact.

Rewrite `this` using `[iterateFrobeniusEquiv_apply, iterateFrobenius_def]`. Then use the resulting hypothesis.
-/
theorem exists_of_pow_eq (r : ℕ) (d : Cb l) (b : OCb l)
    (h : d ^ (l ^ r) = algebraMap (OCb l) (Cb l) b) : ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = d := by
  refine ⟨(iterateFrobeniusEquiv (OCb l) l r).symm b, ?_⟩
  apply iterateFrobenius_inj (Cb l) l r
  rw [iterateFrobenius_def, iterateFrobenius_def, h, ← map_pow]
  congr 1
  have := (iterateFrobeniusEquiv (OCb l) l r).apply_symm_apply b
  rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at this

/- English proof (translation)
Establish `hc : ∀ i, ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = y.coeff i`. Introduce `i`. Take `⟨a, ha⟩` from `hy (i + r + 1)`. Establish `he` using `coeff_eq_of_dvd ha (i + r) (by omega)`. Rewrite `he` using `[coeff_pow_mul_add]`.

Conclude with `exists_of_pow_eq l r _ _ (by rw [he]; exact WittVector.map_coeff _ _ _)`. Use `choose c hc using hc`. Use `⟨WittVector.mk l c, ?_⟩` and prove the remaining obligations. Use extensionality with `i`. Rewrite using `[show inclW l (WittVector.mk l c) = WittVector.map (algebraMap (OCb l) (Cb l)) (WittVector.mk l c) from rfl, WittVector.map_coeff]`.

Conclude with `(hc i).symm`.
-/
theorem mem_range_of_pow_mul (r : ℕ) (y : WCb l)
    (hy : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * y - inclW l a) :
    ∃ a : Ainf l, y = inclW l a := by
  have hc : ∀ i, ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = y.coeff i := by
    intro i
    obtain ⟨a, ha⟩ := hy (i + r + 1)
    have he := coeff_eq_of_dvd ha (i + r) (by omega)
    rw [coeff_pow_mul_add] at he
    exact exists_of_pow_eq l r _ _ (by rw [he]; exact WittVector.map_coeff _ _ _)
  choose c hc using hc
  refine ⟨WittVector.mk l c, ?_⟩
  ext i
  rw [show inclW l (WittVector.mk l c) = WittVector.map (algebraMap (OCb l) (Cb l)) (WittVector.mk l c)
    from rfl, WittVector.map_coeff]
  exact (hc i).symm

/- English proof (translation)
Introduce `l _ ι hu r x hx`. Take `⟨u, hu⟩` from `hu`. Take `⟨a, ha⟩` from `mem_range_of_pow_mul l r (↑u⁻¹ * x) (by`. Introduce `n`. Take `⟨a, w, hw⟩` from `hx n`.

Use `⟨a, ↑u⁻¹ * w, ?_⟩` and prove the remaining obligations. Establish `: (l : WCb l) ^ r * (↑u⁻¹ * x) - inclW l a = ↑u⁻¹ * ((l : WCb l) ^ r * x - inclW l (ι * a))`. Rewrite using `[map_mul, ← hu, mul_sub]`. Rewrite using `[← mul_assoc (↑u⁻¹ : WCb l) (↑u) _, Units.inv_mul, one_mul]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this, hw]`. Use the proof step `ring)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, ← ha, ← hu, ← mul_assoc, Units.mul_inv, one_mul]`.
-/
theorem mem_ideal_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) →
    ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l,
      (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) →
    ∃ a : Ainf l, x = inclW l (ι * a) := by
  intro l _ ι hu r x hx
  obtain ⟨u, hu⟩ := hu
  obtain ⟨a, ha⟩ := mem_range_of_pow_mul l r (↑u⁻¹ * x) (by
    intro n
    obtain ⟨a, w, hw⟩ := hx n
    refine ⟨a, ↑u⁻¹ * w, ?_⟩
    have : (l : WCb l) ^ r * (↑u⁻¹ * x) - inclW l a
        = ↑u⁻¹ * ((l : WCb l) ^ r * x - inclW l (ι * a)) := by
      rw [map_mul, ← hu, mul_sub]
      rw [← mul_assoc (↑u⁻¹ : WCb l) (↑u) _, Units.inv_mul, one_mul]
      ring
    rw [this, hw]; ring)
  refine ⟨a, ?_⟩
  rw [map_mul, ← ha, ← hu, ← mul_assoc, Units.mul_inv, one_mul]

end GlobalTheory.AinfSat
