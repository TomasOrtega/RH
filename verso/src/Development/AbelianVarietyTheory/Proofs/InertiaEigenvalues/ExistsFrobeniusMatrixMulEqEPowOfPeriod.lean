import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMemSpanCoeffPeriodPowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisinStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
open Matrix

namespace GlobalTheory.BSP.HeightAprime

/- English proof (translation)
The claim follows from `| 0, h => by simpa using h | n + 1, h => by obtain ⟨x, hx⟩ := h have hpx : p ∣ a * x := ⟨p ^ n * b, by rw [← hx]; ring⟩ obtain ⟨y, rfl⟩ := (hp.dvd_or_dvd hpx).resolve_left ha refine dvd_of_dvd_prime_pow_mul hp ha n ⟨y, mul_left_cancel₀ hp.ne_zero ?_⟩ linear_combination hx`.
-/
theorem dvd_of_dvd_prime_pow_mul {R : Type} [CommRing R] [IsDomain R] {p a b : R} (hp : Prime p)
    (ha : ¬ p ∣ a) : ∀ n : ℕ, a ∣ p ^ n * b → a ∣ b
  | 0, h => by simpa using h
  | n + 1, h => by
    obtain ⟨x, hx⟩ := h
    have hpx : p ∣ a * x := ⟨p ^ n * b, by rw [← hx]; ring⟩
    obtain ⟨y, rfl⟩ := (hp.dvd_or_dvd hpx).resolve_left ha
    refine dvd_of_dvd_prime_pow_mul hp ha n ⟨y, mul_left_cancel₀ hp.ne_zero ?_⟩
    linear_combination hx

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩ n`. Rewrite using `[coeff_C_mul]`. Conclude with `dvd_mul_right _ _`. Introduce `h`.

Use `⟨mk fun n => (h n).choose, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[coeff_C_mul, coeff_mk]`. Conclude with `(h n).choose_spec`.
-/
theorem C_dvd_iff {R : Type} [CommRing R] (p : R) (f : R⟦X⟧) :
    C p ∣ f ↔ ∀ n, p ∣ coeff n f := by
  constructor
  · rintro ⟨g, rfl⟩ n
    rw [coeff_C_mul]; exact dvd_mul_right _ _
  · intro h
    refine ⟨mk fun n => (h n).choose, ?_⟩
    ext n
    rw [coeff_C_mul, coeff_mk]
    exact (h n).choose_spec

/- English proof (translation)
Use `haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp`. Set `q : R →+* R ⧸ Ideal.span {p}` to `Ideal.Quotient.mk _`. Establish `key : ∀ f : R⟦X⟧, C p ∣ f ↔ PowerSeries.map q f = 0`. Introduce `f`. Rewrite using `[C_dvd_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Use extensionality with `n`. Rewrite using `[coeff_map, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h n))`.

Introduce `h n`. Use `congrArg (coeff n) h` as an intermediate fact. Rewrite `this` using `[coeff_map, map_zero]`. Conclude with `Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)`. Use `⟨fun h => hp.ne_zero (by simpa using congrArg (constantCoeff) h), fun h => hp.not_unit ?_, ?_⟩` and prove the remaining obligations.

Simplify using `using h.map (constantCoeff (R := R))`. Introduce `f g hfg`. Rewrite using `[key, key]`. Rewrite `hfg` using `[key, map_mul]`. Conclude with `mul_eq_zero.1 hfg`.
-/
theorem prime_C {R : Type} [CommRing R] [IsDomain R] {p : R} (hp : Prime p) : Prime (C p : R⟦X⟧) := by
  haveI : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  let q : R →+* R ⧸ Ideal.span {p} := Ideal.Quotient.mk _
  have key : ∀ f : R⟦X⟧, C p ∣ f ↔ PowerSeries.map q f = 0 := by
    intro f
    rw [C_dvd_iff]
    constructor
    · intro h; ext n
      rw [coeff_map, map_zero]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton.2 (h n))
    · intro h n
      have := congrArg (coeff n) h
      rw [coeff_map, map_zero] at this
      exact Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 this)
  refine ⟨fun h => hp.ne_zero (by simpa using congrArg (constantCoeff) h), fun h => hp.not_unit ?_, ?_⟩
  · simpa using h.map (constantCoeff (R := R))
  · intro f g hfg
    rw [key, key]
    rw [key, map_mul] at hfg
    exact mul_eq_zero.1 hfg

/- English proof (translation)
Establish `h : Prime (l : Wq l a)` using `(WittVector.irreducible l).prime`. Use `prime_C h` as an intermediate fact. Simplify using `using this`.
-/
theorem prime_l {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] : Prime (l : (Wq l a)⟦X⟧) := by
  have h : Prime (l : Wq l a) := (WittVector.irreducible l).prime
  have := prime_C h
  simpa using this

end GlobalTheory.BSP.HeightAprime

namespace GlobalTheory.BSP.HeightAprime

variable {l : ℕ} [hl : Fact l.Prime]

/- English proof (translation)
Introduce and unpack `⟨t, ht⟩`. Establish `h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det`. Rewrite using `[RingHom.map_det, RingHom.map_det, ← det_mul]`. Conclude with `congrArg det hφ`. Establish `h0` using `congrArg WittVector.constantCoeff h2`.

Rewrite `h0` using `[ht, map_mul, map_mul, map_mul, map_natCast, map_natCast, CharP.cast_eq_zero, zero_mul, mul_zero]`. Establish `hc : (WittVector.frobenius Y.det).coeff 0 = Y.det.coeff 0 ^ l` using `WittVector.coeff_frobenius_charP l _ 0`. Establish `hz : Y.det.coeff 0 = 0`. Establish `: WittVector.constantCoeff (WittVector.frobenius Y.det) = (WittVector.frobenius Y.det).coeff 0` using `rfl`. Rewrite `h0` using `[this, hc]`.

Conclude with `pow_eq_zero_iff hl.out.ne_zero |>.1 h0`. Establish `hu : IsUnit (inclW l Y.det)`. Rewrite using `[RingHom.map_det]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 hY`. Establish `hu0` using `hu.map (WittVector.constantCoeff (p := l) (R := Cb l))`.

Establish `: WittVector.constantCoeff (inclW l Y.det) = (inclW l Y.det).coeff 0` using `rfl`. Rewrite `hu0` using `[this, inclW, WittVector.map_coeff, hz, map_zero]`. Conclude with `not_isUnit_zero hu0`.
-/
theorem not_l_dvd_det {K : FinExt l} (bk : BK K) {d : ℕ} (Y : Matrix (Fin d) (Fin d) (Ainf l))
    (A : Matrix (Fin d) (Fin d) bk.S) (hY : IsUnit (Y.map (inclW l)))
    (hφ : Y.map WittVector.frobenius = Y * A.map bk.ev) : ¬ (l : bk.S) ∣ A.det := by
  rintro ⟨t, ht⟩
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h0 := congrArg WittVector.constantCoeff h2
  rw [ht, map_mul, map_mul, map_mul, map_natCast, map_natCast, CharP.cast_eq_zero, zero_mul, mul_zero] at h0
  have hc : (WittVector.frobenius Y.det).coeff 0 = Y.det.coeff 0 ^ l :=
    WittVector.coeff_frobenius_charP l _ 0
  have hz : Y.det.coeff 0 = 0 := by
    have : WittVector.constantCoeff (WittVector.frobenius Y.det) = (WittVector.frobenius Y.det).coeff 0 := rfl
    rw [this, hc] at h0
    exact pow_eq_zero_iff hl.out.ne_zero |>.1 h0
  have hu : IsUnit (inclW l Y.det) := by
    rw [RingHom.map_det]; exact (Matrix.isUnit_iff_isUnit_det _).1 hY
  have hu0 := hu.map (WittVector.constantCoeff (p := l) (R := Cb l))
  have : WittVector.constantCoeff (inclW l Y.det) = (inclW l Y.det).coeff 0 := rfl
  rw [this, inclW, WittVector.map_coeff, hz, map_zero] at hu0
  exact not_isUnit_zero hu0

end GlobalTheory.BSP.HeightAprime

/- English proof (translation)
Introduce `l _ K bk τ hτ d Y S' A k M hY hYS hφ`. Establish `h1 : Y.det * S'.det = ((l : Ainf l) ^ k * τ ^ M) ^ d`. Rewrite using `[← det_mul, hYS, det_smul, det_one, mul_one, Fintype.card_fin]`. Establish `h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det`. Rewrite using `[RingHom.map_det, RingHom.map_det, ← det_mul]`.

Conclude with `congrArg det hφ`. Establish `h3 : bk.ev A.det * (Y.det * WittVector.frobenius S'.det) = bk.ev ((l : bk.S) ^ (k * d) * bk.E ^ (M * d)) * τ ^ (M * d)`. Use `congrArg WittVector.frobenius h1` as an intermediate fact. Rewrite `this` using `[map_mul, h2, map_pow, map_mul, map_pow, map_pow, map_natCast, hτ.1]`. Rewrite using `[map_mul, map_pow, map_pow, map_natCast, pow_mul, pow_mul, pow_mul]`.

Take the linear combination `this`. Take `⟨ι, ⟨TB⟩⟩` from `GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk`. Take `⟨r, hr⟩` from `GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (M * d)`. Use `set c : bk.S := (l : bk.S) ^ (k * d) * bk.E ^ (M * d)`. Establish `hdiv : ∀ i, A.det ∣ c * TB.c i (τ ^ (M * d))` using `fun i => by`.

Use `congrArg (TB.c i) h3` as an intermediate fact. Rewrite `this` using `[TB.c_mul, TB.c_mul]`. Conclude with `⟨_, this.symm⟩`. Establish `hdvd : A.det ∣ c * (l : bk.S) ^ r`. Use `Submodule.span_induction (p := fun x _ => A.det ∣ c * x) ?_ ?_ ?_ ?_ hr` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hdiv i`. Simplify using the standard rewrite rules. Introduce `x y _ _ hx hy`. Rewrite using `[mul_add]`.

Conclude with `dvd_add hx hy`. Introduce `a x _ hx`. Rewrite using `[smul_eq_mul, mul_left_comm]`. Conclude with `dvd_mul_of_dvd_right hx a`. Establish `hdvd' : A.det ∣ (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d)`.

Establish `e : c * (l : bk.S) ^ r = (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d)`. Simplify using `only [c]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hdvd` using `[e]`. Then use the resulting hypothesis. Take `⟨q, hq⟩` from `GlobalTheory.BSP.HeightAprime.dvd_of_dvd_prime_pow_mul (GlobalTheory.BSP.HeightAprime.prime_l bk.a) (GlobalTheory.BSP.HeightAprime.not_l_dvd_det bk Y A hY hφ) _ hdvd'`.

Use `⟨M * d, q • A.adjugate, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_smul, mul_adjugate, smul_smul, mul_comm q, ← hq]`.
-/
theorem GlobalTheory.BSP.HeightAprime.main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (τ : Ainf l), bk.IsPer τ → ∀ (d : ℕ) (Y S' : Matrix (Fin d) (Fin d) (Ainf l)) (A : Matrix (Fin d) (Fin d) (bk.S)) (k M : ℕ), IsUnit (Y.map (inclW l)) → Y * S' = ((l : Ainf l) ^ k * τ ^ M) • (1 : Matrix (Fin d) (Fin d) (Ainf l)) → Y.map WittVector.frobenius = Y * A.map bk.ev → ∃ (b : ℕ) (A' : Matrix (Fin d) (Fin d) (bk.S)), A * A' = bk.E ^ b • (1 : Matrix (Fin d) (Fin d) (bk.S)) := by
  intro l _ K bk τ hτ d Y S' A k M hY hYS hφ
  have h1 : Y.det * S'.det = ((l : Ainf l) ^ k * τ ^ M) ^ d := by
    rw [← det_mul, hYS, det_smul, det_one, mul_one, Fintype.card_fin]
  have h2 : WittVector.frobenius Y.det = Y.det * bk.ev A.det := by
    rw [RingHom.map_det, RingHom.map_det, ← det_mul]
    exact congrArg det hφ
  have h3 : bk.ev A.det * (Y.det * WittVector.frobenius S'.det) =
      bk.ev ((l : bk.S) ^ (k * d) * bk.E ^ (M * d)) * τ ^ (M * d) := by
    have := congrArg WittVector.frobenius h1
    rw [map_mul, h2, map_pow, map_mul, map_pow, map_pow, map_natCast, hτ.1] at this
    rw [map_mul, map_pow, map_pow, map_natCast, pow_mul, pow_mul, pow_mul]
    linear_combination this
  obtain ⟨ι, ⟨TB⟩⟩ := GlobalTheory.T.ainf_adicTopologicalBasis_over_breuilKisin l K bk
  obtain ⟨r, hr⟩ := GlobalTheory.T.exists_pow_mem_span_coeff_period_pow l K bk τ hτ ι TB (M * d)
  set c : bk.S := (l : bk.S) ^ (k * d) * bk.E ^ (M * d)
  have hdiv : ∀ i, A.det ∣ c * TB.c i (τ ^ (M * d)) := fun i => by
    have := congrArg (TB.c i) h3
    rw [TB.c_mul, TB.c_mul] at this
    exact ⟨_, this.symm⟩
  have hdvd : A.det ∣ c * (l : bk.S) ^ r := by
    refine Submodule.span_induction (p := fun x _ => A.det ∣ c * x) ?_ ?_ ?_ ?_ hr
    · rintro _ ⟨i, rfl⟩; exact hdiv i
    · simp
    · intro x y _ _ hx hy; rw [mul_add]; exact dvd_add hx hy
    · intro a x _ hx; rw [smul_eq_mul, mul_left_comm]; exact dvd_mul_of_dvd_right hx a
  have hdvd' : A.det ∣ (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
    have e : c * (l : bk.S) ^ r = (l : bk.S) ^ (k * d + r) * bk.E ^ (M * d) := by
      simp only [c]; ring
    rwa [e] at hdvd
  obtain ⟨q, hq⟩ := GlobalTheory.BSP.HeightAprime.dvd_of_dvd_prime_pow_mul (GlobalTheory.BSP.HeightAprime.prime_l bk.a)
    (GlobalTheory.BSP.HeightAprime.not_l_dvd_det bk Y A hY hφ) _ hdvd'
  refine ⟨M * d, q • A.adjugate, ?_⟩
  rw [Matrix.mul_smul, mul_adjugate, smul_smul, mul_comm q, ← hq]
