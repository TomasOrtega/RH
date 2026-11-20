import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
open GlobalTheory.Col PowerSeries

noncomputable section
namespace GlobalTheory.Col.NormFrob

/- English proof (translation)
Use `ext1 h`. Use extensionality with `n`. Use `set P : Polynomial R := trunc (n + 1) h`. Establish `hd : X ^ (n + 1) ∣ h - (P : PowerSeries R)`. Rewrite using `[X_pow_dvd_iff]`.

Introduce `m hm`. Simplify using `[P, Polynomial.coeff_coe, coeff_trunc, hm]`. Take `⟨q, hq⟩` from `hd`. Establish `hh : h = (P : PowerSeries R) + X ^ (n + 1) * q` using `by rw [← hq]; ring`. Establish `hP : f (P : PowerSeries R) = g (P : PowerSeries R)`.

Use `congrArg (fun F => F P) hfg` as an intermediate fact. Simplify using `using this`. Establish `key : ∀ F : PowerSeries R →+* PowerSeries S, X ∣ F X → coeff n (F (X ^ (n + 1) * q)) = 0`. Introduce `F hF`. Establish `: X ^ (n + 1) ∣ F (X ^ (n + 1) * q)`.

Rewrite using `[map_mul, map_pow]`. Conclude with `Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hF _) _`. Conclude with `(X_pow_dvd_iff.1 this) n (Nat.lt_succ_self n)`. Rewrite using `[hh, map_add, map_add, map_add, map_add, hP, key f hf, key g hg]`.
-/
theorem ringHom_ext_of_poly {R S : Type} [CommRing R] [CommRing S] (f g : PowerSeries R →+* PowerSeries S)
    (hfg : f.comp Polynomial.coeToPowerSeries.ringHom = g.comp Polynomial.coeToPowerSeries.ringHom)
    (hf : X ∣ f X) (hg : X ∣ g X) : f = g := by
  ext1 h
  ext n
  set P : Polynomial R := trunc (n + 1) h
  have hd : X ^ (n + 1) ∣ h - (P : PowerSeries R) := by
    rw [X_pow_dvd_iff]
    intro m hm
    simp [P, Polynomial.coeff_coe, coeff_trunc, hm]
  obtain ⟨q, hq⟩ := hd
  have hh : h = (P : PowerSeries R) + X ^ (n + 1) * q := by rw [← hq]; ring
  have hP : f (P : PowerSeries R) = g (P : PowerSeries R) := by
    have := congrArg (fun F => F P) hfg
    simpa using this
  have key : ∀ F : PowerSeries R →+* PowerSeries S, X ∣ F X → coeff n (F (X ^ (n + 1) * q)) = 0 := by
    intro F hF
    have : X ^ (n + 1) ∣ F (X ^ (n + 1) * q) := by
      rw [map_mul, map_pow]
      exact Dvd.dvd.mul_right (pow_dvd_pow_of_dvd hF _) _
    exact (X_pow_dvd_iff.1 this) n (Nat.lt_succ_self n)
  rw [hh, map_add, map_add, map_add, map_add, hP, key f hf, key g hg]

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

abbrev red : PowerSeries R →+* PowerSeries (R ⧸ Ideal.span {(p : R)}) :=
  PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)}))

/- English proof (translation)
Establish `hc : ∀ n, ∃ c : R, coeff n D = (p : R) * c`. Introduce `n`. Establish `h1 : coeff n (red p D) = 0` using `by rw [hD, map_zero]`. Rewrite `h1` using `[coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']`. Take `⟨c, hc⟩` from `h1`.

Conclude with `⟨c, by rw [← hc, mul_comm]⟩`. Use `choose c hc using hc`. Use `⟨PowerSeries.mk c, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[hc n, show (p : PowerSeries R) = C (p : R) from (map_natCast C p).symm, coeff_C_mul, coeff_mk]`.
-/
theorem exists_of_red_eq_zero (D : PowerSeries R) (hD : red p D = 0) :
    ∃ g : PowerSeries R, D = (p : PowerSeries R) * g := by
  have hc : ∀ n, ∃ c : R, coeff n D = (p : R) * c := by
    intro n
    have h1 : coeff n (red p D) = 0 := by rw [hD, map_zero]
    rw [coeff_map, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    exact ⟨c, by rw [← hc, mul_comm]⟩
  choose c hc using hc
  refine ⟨PowerSeries.mk c, ?_⟩
  ext n
  rw [hc n, show (p : PowerSeries R) = C (p : R) from (map_natCast C p).symm, coeff_C_mul, coeff_mk]

/- English proof (translation)
Use `haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)`. Use `haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p := charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p`. Establish `hX1 : ((frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p)) X = X ^ p`. Simplify using `[frobenius_def]`. Establish `hX2 : ((red p).comp ((phi (R` using `R) p hp.out.pos).toRingHom.comp (smap σ))) X = X ^ p := by`.

Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, smap, map_X, phi_X, map_sub, map_pow, map_add, map_one]`. Rewrite using `[add_pow_char, one_pow, add_sub_cancel_left]`. It suffices to establish `H : (frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p) = (red p).comp ((phi (R` using `R) p hp.out.pos).toRingHom.comp (smap σ)) by`. Use `congrArg (fun F => F h) H` as an intermediate fact. Simplify `this` using `[frobenius_def]`.

Apply `ringHom_ext_of_poly` to reduce the goal to its premises. Apply `Polynomial.ringHom_ext` to reduce the goal to its premises. Introduce `a`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, smap, map_C, frobenius_def, ← map_pow]`. Establish `h1 : (phi (R` using `R) p hp.out.pos) (C (σ a)) = C (σ a) := (phi (R := R) p hp.out.pos).commutes (σ a)`.

Establish `h2 : Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ a) = (Ideal.Quotient.mk (Ideal.span {(p : R)}) a) ^ p`. Rewrite using `[← map_pow]`. Conclude with `Ideal.Quotient.eq.2 (hfl.frob a)`. Rewrite using `[h1, map_C, h2, map_pow]`. Simplify using `only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]`.

Rewrite `hX1`, `hX2` using `[RingHom.comp_apply]`. Rewrite `*` using `[hX1, RingHom.comp_apply]`. Rewrite using `[hX2]`. Rewrite using `[hX1]`. Conclude with `dvd_pow_self _ hp.out.ne_zero`.

Rewrite using `[hX2]`. Conclude with `dvd_pow_self _ hp.out.ne_zero`.
-/
theorem red_pow_eq (σ : R ≃+* R) (hfl : FrobLift R p σ) (h : PowerSeries R) :
    red p h ^ p = red p (phi (R := R) p hp.out.pos (smap σ h)) := by
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  have hX1 : ((frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p)) X = X ^ p := by
    simp [frobenius_def]
  have hX2 : ((red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ))) X = X ^ p := by
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, smap, map_X, phi_X, map_sub, map_pow,
      map_add, map_one]
    rw [add_pow_char, one_pow, add_sub_cancel_left]
  suffices H : (frobenius (PowerSeries (R ⧸ Ideal.span {(p : R)})) p).comp (red p) =
      (red p).comp ((phi (R := R) p hp.out.pos).toRingHom.comp (smap σ)) by
    have := congrArg (fun F => F h) H
    simpa [frobenius_def] using this
  apply ringHom_ext_of_poly
  · apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.coeToPowerSeries.ringHom_apply,
        Polynomial.coe_C, smap, map_C, frobenius_def, ← map_pow]
      have h1 : (phi (R := R) p hp.out.pos) (C (σ a)) = C (σ a) := (phi (R := R) p hp.out.pos).commutes (σ a)
      have h2 : Ideal.Quotient.mk (Ideal.span {(p : R)}) (σ a) = (Ideal.Quotient.mk (Ideal.span {(p : R)}) a) ^ p := by
        rw [← map_pow]; exact Ideal.Quotient.eq.2 (hfl.frob a)
      rw [h1, map_C, h2, map_pow]
    · simp only [RingHom.comp_apply, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_X]
      rw [RingHom.comp_apply] at hX1 hX2
      rw [hX1, RingHom.comp_apply] at *
      rw [hX2]
  · rw [hX1]; exact dvd_pow_self _ hp.out.ne_zero
  · rw [hX2]; exact dvd_pow_self _ hp.out.ne_zero

end GlobalTheory.Col.NormFrob

namespace GlobalTheory.Col.NormFrob
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/- English proof (translation)
Use `haveI := hfl.dom`. Use `haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)`. Use `haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p := charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p`. Use `haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hfl.prime.ne_zero).2 hfl.prime`. Use `letI := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra`.

Use `letI : Module (PowerSeries R) (PowerSeries R) := Algebra.toModule`. Use `haveI : Module.Free (PowerSeries R) (PowerSeries R) := Module.Free.of_basis b`. Establish `hrank : Module.finrank (PowerSeries R) (PowerSeries R) = p`. Rewrite using `[Module.finrank_eq_card_basis b, Fintype.card_fin]`. Establish `hred0 : red p (p : PowerSeries R) = 0`.

Rewrite using `[map_natCast]`. Conclude with `CharP.cast_eq_zero _ p`. Establish `hcong : ∀ x g : PowerSeries R, red p (Algebra.norm (PowerSeries R) (x + (p : PowerSeries R) * g)) = red p (Algebra.norm (PowerSeries R) x)`. Introduce `x g`. Rewrite using `[Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, RingHom.map_det, RingHom.map_det, map_add, map_mul, map_natCast, map_add, map_mul, map_natCast]`.

Establish `hz : ((p : ℕ) : Matrix (Fin p) (Fin p) (PowerSeries (R ⧸ Ideal.span {(p : R)}))) = 0`. Use extensionality with `i j`. Rewrite using `[Matrix.natCast_apply]`. Apply the tactic sequence `split_ifs <;> simp [CharP.cast_eq_zero]`. Rewrite using `[hz, zero_mul, add_zero]`.

Take `⟨g, hg⟩` from `exists_of_red_eq_zero p (h ^ p - phi (R := R) p hp.out.pos (smap σ h)) (by`. Rewrite using `[map_sub, map_pow, red_pow_eq p σ hfl h, sub_self])`. Establish `hpow : red p (normOp p h) ^ p = red p (smap σ h) ^ p`. Establish `e1 : h ^ p = phi (R` using `R) p hp.out.pos (smap σ h) + (p : PowerSeries R) * g := by rw [← hg]; ring`. Establish `e2 : Algebra.norm (PowerSeries R) (phi (R` using `R) p hp.out.pos (smap σ h)) = (smap σ h) ^ p := by`.

Use `Algebra.norm_algebraMap (S := PowerSeries R) (smap σ h)` as an intermediate fact. Rewrite `this` using `[hrank]`. Conclude with `this`. Unfold `normOp`. Rewrite using `[← map_pow, ← map_pow (Algebra.norm _), e1, hcong, e2, map_pow]`.

Establish `hinj` using `frobenius_inj (PowerSeries (R ⧸ Ideal.span {(p : R)})) p`. Establish `heq : red p (normOp p h) = red p (smap σ h)` using `hinj (by simpa [frobenius_def] using hpow)`. Take `⟨r, hr⟩` from `exists_of_red_eq_zero p (normOp p h - smap σ h) (by rw [map_sub, heq, sub_self])`. Conclude with `⟨r, by rw [← hr]; ring⟩`.
-/
theorem normOp_eq_smap_add (σ : R ≃+* R) (hfl : FrobLift R p σ)
    (b : @Module.Basis (Fin p) (PowerSeries R) (PowerSeries R) _ _
      ((phi (R := R) p hp.out.pos).toRingHom.toAlgebra.toModule)) (h : PowerSeries R) :
    ∃ r : PowerSeries R, normOp p h = smap σ h + (p : PowerSeries R) * r := by
  haveI := hfl.dom
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p (hfl.prime.not_unit)
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_algebraMap (R := R ⧸ Ideal.span {(p : R)}) (PowerSeries.C_injective) p
  haveI : (Ideal.span {(p : R)}).IsPrime := (Ideal.span_singleton_prime hfl.prime.ne_zero).2 hfl.prime
  letI := (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
  letI : Module (PowerSeries R) (PowerSeries R) := Algebra.toModule
  haveI : Module.Free (PowerSeries R) (PowerSeries R) := Module.Free.of_basis b
  have hrank : Module.finrank (PowerSeries R) (PowerSeries R) = p := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hred0 : red p (p : PowerSeries R) = 0 := by
    rw [map_natCast]; exact CharP.cast_eq_zero _ p

  have hcong : ∀ x g : PowerSeries R,
      red p (Algebra.norm (PowerSeries R) (x + (p : PowerSeries R) * g)) = red p (Algebra.norm (PowerSeries R) x) := by
    intro x g
    rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det b, RingHom.map_det, RingHom.map_det, map_add,
      map_mul, map_natCast, map_add, map_mul, map_natCast]
    have hz : ((p : ℕ) : Matrix (Fin p) (Fin p) (PowerSeries (R ⧸ Ideal.span {(p : R)}))) = 0 := by
      ext i j
      rw [Matrix.natCast_apply]
      split_ifs <;> simp [CharP.cast_eq_zero]
    rw [hz, zero_mul, add_zero]
  obtain ⟨g, hg⟩ := exists_of_red_eq_zero p (h ^ p - phi (R := R) p hp.out.pos (smap σ h)) (by
    rw [map_sub, map_pow, red_pow_eq p σ hfl h, sub_self])
  have hpow : red p (normOp p h) ^ p = red p (smap σ h) ^ p := by
    have e1 : h ^ p = phi (R := R) p hp.out.pos (smap σ h) + (p : PowerSeries R) * g := by rw [← hg]; ring
    have e2 : Algebra.norm (PowerSeries R) (phi (R := R) p hp.out.pos (smap σ h)) = (smap σ h) ^ p := by
      have := Algebra.norm_algebraMap (S := PowerSeries R) (smap σ h)
      rw [hrank] at this; exact this
    unfold normOp
    rw [← map_pow, ← map_pow (Algebra.norm _), e1, hcong, e2, map_pow]
  have hinj := frobenius_inj (PowerSeries (R ⧸ Ideal.span {(p : R)})) p
  have heq : red p (normOp p h) = red p (smap σ h) := hinj (by simpa [frobenius_def] using hpow)
  obtain ⟨r, hr⟩ := exists_of_red_eq_zero p (normOp p h - smap σ h) (by rw [map_sub, heq, sub_self])
  exact ⟨r, by rw [← hr]; ring⟩

end GlobalTheory.Col.NormFrob
