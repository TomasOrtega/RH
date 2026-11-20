import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime

noncomputable section
open PowerSeries
namespace GlobalTheory.Col.Model
open GlobalTheory.Col

/- English proof (translation)
The claim follows from `inferInstance prime := (WittVector.irreducible p).prime complete := inferInstance frob := by intro x rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero] have : (WittVector.constantCoeff : WittVector p k →+* k) (WittVector.frobeniusEquiv p k x - x ^ p) = 0 := by rw [map_sub, map_pow …`.
-/
theorem frobLift_witt (p : ℕ) [hp : Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] :
    FrobLift (WittVector p k) p (WittVector.frobeniusEquiv p k) where
  dom := inferInstance
  prime := (WittVector.irreducible p).prime
  complete := inferInstance
  frob := by
    intro x
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have : (WittVector.constantCoeff : WittVector p k →+* k) (WittVector.frobeniusEquiv p k x - x ^ p) = 0 := by
      rw [map_sub, map_pow]
      simp [WittVector.frobeniusEquiv, WittVector.coeff_frobenius_charP]
    simpa using this
  perfect := by
    intro x
    obtain ⟨y, hy⟩ := (PerfectRing.bijective_frobenius (R := k) (p := p)).2 (x.coeff 0)
    refine ⟨WittVector.teichmuller p y, ?_⟩
    rw [WittVector.mem_span_p_iff_coeff_zero_eq_zero]
    have : (WittVector.constantCoeff : WittVector p k →+* k) (WittVector.teichmuller p y ^ p - x) = 0 := by
      rw [map_sub, map_pow]
      simpa [sub_eq_zero] using hy
    simpa using this

/- English proof (translation)
The claim follows from `frobLift_witt p _`.
-/
theorem frobLift_witt_closure (p : ℕ) [hp : Fact p.Prime] :
    FrobLift (WittVector p (AlgebraicClosure (ZMod p))) p (WittVector.frobeniusEquiv p (AlgebraicClosure (ZMod p))) :=
  frobLift_witt p _

section Free
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

abbrev om : PowerSeries R := (1 + X) ^ p - 1

/- English proof (translation)
Use `haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p hu`. Use `haveI : Nontrivial (R ⧸ Ideal.span {(p : R)}) := CharP.nontrivial_of_char_ne_one (R := R ⧸ Ideal.span {(p : R)}) hp.out.ne_one`. Use `haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p := charP_of_injective_ringHom (f := PowerSeries.C) PowerSeries.C_injective p`. Establish `: (om p : PowerSeries R).map (Ideal.Quotient.mk (Ideal.span {(p : R)})) = X ^ p`. Simplify using `only [om, map_sub, map_pow, map_add, map_one, PowerSeries.map_X]`.

Rewrite using `[add_pow_char]`. Simplify using the standard rewrite rules. Rewrite using `[this, order_X_pow]`. Simplify using the standard rewrite rules.
-/
theorem om_order (hu : (p : R) ∈ nonunits R) :
    ((om p : PowerSeries R).map (Ideal.Quotient.mk (Ideal.span {(p : R)}))).order.toNat = p := by
  haveI : CharP (R ⧸ Ideal.span {(p : R)}) p := CharP.quotient R p hu
  haveI : Nontrivial (R ⧸ Ideal.span {(p : R)}) := CharP.nontrivial_of_char_ne_one (R := R ⧸ Ideal.span {(p : R)}) hp.out.ne_one
  haveI : CharP (PowerSeries (R ⧸ Ideal.span {(p : R)})) p :=
    charP_of_injective_ringHom (f := PowerSeries.C) PowerSeries.C_injective p
  have : (om p : PowerSeries R).map (Ideal.Quotient.mk (Ideal.span {(p : R)})) = X ^ p := by
    simp only [om, map_sub, map_pow, map_add, map_one, PowerSeries.map_X]
    rw [add_pow_char]; simp
  rw [this, order_X_pow]; simp

/- English proof (translation)
Unfold `IsWeierstrassDivisorAt`. Rewrite using `[om_order p hu]`. Establish `h : ((1 + X) ^ p : PowerSeries R) = (((1 + Polynomial.X) ^ p : Polynomial R) : PowerSeries R)` using `by simp`. Establish `: coeff p (om p : PowerSeries R) = 1`. Rewrite using `[om, map_sub, h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, coeff_one, if_neg hp.out.ne_zero]`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `isUnit_one`.
-/
theorem om_div (hu : (p : R) ∈ nonunits R) : (om p : PowerSeries R).IsWeierstrassDivisorAt (Ideal.span {(p : R)}) := by
  unfold IsWeierstrassDivisorAt
  rw [om_order p hu]
  have h : ((1 + X) ^ p : PowerSeries R) = (((1 + Polynomial.X) ^ p : Polynomial R) : PowerSeries R) := by simp
  have : coeff p (om p : PowerSeries R) = 1 := by
    rw [om, map_sub, h, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, coeff_one, if_neg hp.out.ne_zero]; simp
  rw [this]; exact isUnit_one

/- English proof (translation)
Rewrite using `[map_add, map_mul, phi_X]`. Use `congr 1`. Conclude with `(phi (R := R) p hp.out.pos).commutes c`.
-/
theorem phi_split (c : R) (g : PowerSeries R) : phi p hp.out.pos (C c + X * g) = C c + om p * phi p hp.out.pos g := by
  rw [map_add, map_mul, phi_X]
  congr 1
  exact (phi (R := R) p hp.out.pos).commutes c

/- English proof (translation)
Use extensionality with `n`. Conclude with `(X_pow_dvd_iff.1 (h (n + 1))) n (Nat.lt_succ_self n)`.
-/
theorem eq_zero_of_X_pow_dvd (f : PowerSeries R) (h : ∀ n, X ^ n ∣ f) : f = 0 := by
  ext n
  exact (X_pow_dvd_iff.1 (h (n + 1))) n (Nat.lt_succ_self n)

variable [IsAdicComplete (Ideal.span {(p : R)}) R]

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Establish `h : ∀ n, ∃ c : R, coeff n g = p * c` using `fun n => by`. Use `congrArg (coeff n) hg` as an intermediate fact. Rewrite `this` using `[coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Conclude with `this`. Use `choose c hc using h`.

Conclude with `⟨PowerSeries.mk c, by ext n; simp [hc]⟩`.
-/
private lemma exists_eq_smul_of_map_quotient_eq_zero (g : R⟦X⟧)
    (hg : PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) g = 0) :
    ∃ d : R⟦X⟧, g = (p : R) • d := by
  have h : ∀ n, ∃ c : R, coeff n g = p * c := fun n => by
    have := congrArg (coeff n) hg
    rw [coeff_map, map_zero, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
    exact this
  choose c hc using h
  exact ⟨PowerSeries.mk c, by ext n; simp [hc]⟩

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Establish `h : ((1 : PowerSeries R) + X) ^ p = (((1 + Polynomial.X) ^ p : Polynomial R) : PowerSeries R)`. Simplify using the standard rewrite rules. Rewrite using `[h, map_sub, map_sub, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, coeff_one, coeff_X_pow]`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases. Simplify using `[hp.out.ne_zero.symm]`.

Distinguish the cases in `hnp : n = p`. Substitute `hnp` using the available equality. Simplify using `[hp.out.ne_zero]`. Distinguish the cases in `hlt : n < p`. Rewrite using `[if_neg hn.ne', if_neg hnp, sub_zero, sub_zero]`.

Conclude with `Nat.cast_dvd_cast (Nat.Prime.dvd_choose_self hp.out hn.ne' hlt)`. Rewrite using `[Nat.choose_eq_zero_of_lt (by omega), if_neg hn.ne', if_neg hnp]`. Simplify using the standard rewrite rules.
-/
private lemma prime_dvd_coeff_one_add_X_pow_sub_one_sub_X_pow (n : ℕ) :
    (p : R) ∣ coeff n (((1 : PowerSeries R) + X) ^ p - 1 - X ^ p) := by
  have h : ((1 : PowerSeries R) + X) ^ p = (((1 + Polynomial.X) ^ p : Polynomial R) : PowerSeries R) := by
    simp
  rw [h, map_sub, map_sub, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow, coeff_one, coeff_X_pow]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hp.out.ne_zero.symm]
  · by_cases hnp : n = p
    · subst hnp; simp [hp.out.ne_zero]
    · by_cases hlt : n < p
      · rw [if_neg hn.ne', if_neg hnp, sub_zero, sub_zero]
        exact Nat.cast_dvd_cast (Nat.Prime.dvd_choose_self hp.out hn.ne' hlt)
      · rw [Nat.choose_eq_zero_of_lt (by omega), if_neg hn.ne', if_neg hnp]
        simp

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Use extensionality with `n`. Rewrite using `[coeff_map, coeff_map, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub]`. Conclude with `prime_dvd_coeff_one_add_X_pow_sub_one_sub_X_pow p n`.
-/
private lemma map_quotient_one_add_X_pow_sub_one :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) ((1 + X) ^ p - 1 : R⟦X⟧) =
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (X ^ p) := by
  ext n
  rw [coeff_map, coeff_map, Ideal.Quotient.eq, Ideal.mem_span_singleton, ← map_sub]
  exact prime_dvd_coeff_one_add_X_pow_sub_one_sub_X_pow p n

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Unfold `_root_.GlobalTheory.Col.phi`. Rewrite using `[PowerSeries.coe_substAlgHom, expand_apply]`. Establish `h1` using `map_subst (_root_.GlobalTheory.Col.hasSubst_om (R := R) p hp.out.pos) (h := Ideal.Quotient.mk (Ideal.span {(p : R)})) f`. Establish `h2` using `map_subst (HasSubst.X_pow (R := R) hp.out.ne_zero) (h := Ideal.Quotient.mk (Ideal.span {(p : R)})) f`. Express the relevant statement in the definitionally equal form `MvPowerSeries.map _ _ = MvPowerSeries.map _ _`.

Rewrite using `[h1, h2]`. Use `congr 1`. Conclude with `map_quotient_one_add_X_pow_sub_one p`.
-/
private lemma map_quotient_phi_eq_map_expand (f : R⟦X⟧) :
    PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (_root_.GlobalTheory.Col.phi p hp.out.pos f) =
      PowerSeries.map (Ideal.Quotient.mk (Ideal.span {(p : R)})) (expand p hp.out.ne_zero f) := by
  unfold _root_.GlobalTheory.Col.phi
  rw [PowerSeries.coe_substAlgHom, expand_apply]
  have h1 := map_subst (_root_.GlobalTheory.Col.hasSubst_om (R := R) p hp.out.pos)
    (h := Ideal.Quotient.mk (Ideal.span {(p : R)})) f
  have h2 := map_subst (HasSubst.X_pow (R := R) hp.out.ne_zero)
    (h := Ideal.Quotient.mk (Ideal.span {(p : R)})) f
  change MvPowerSeries.map _ _ = MvPowerSeries.map _ _
  rw [h1, h2]
  congr 1
  exact map_quotient_one_add_X_pow_sub_one p

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
The claim follows from `exists_eq_smul_of_map_quotient_eq_zero p _ (by rw [map_sub, map_quotient_phi_eq_map_expand, sub_self])`.
-/
private lemma exists_phi_sub_expand_eq_smul (f : R⟦X⟧) :
    ∃ d : R⟦X⟧, _root_.GlobalTheory.Col.phi p hp.out.pos f - expand p hp.out.ne_zero f = (p : R) • d :=
  exists_eq_smul_of_map_quotient_eq_zero p _ (by rw [map_sub, map_quotient_phi_eq_map_expand, sub_self])

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Use `choose d hd using fun i => exists_phi_sub_expand_eq_smul p (g i)`. Use `⟨∑ i, d i * X ^ (i : ℕ), ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_mul_assoc, ← hd i]`.

Expand and normalize the polynomial expressions, which then agree.
-/
private lemma exists_sum_phi_eq_sum_expand_add_smul (g : Fin p → R⟦X⟧) :
    ∃ D : R⟦X⟧, ∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (g i) * X ^ (i : ℕ) =
      ∑ i, expand p hp.out.ne_zero (g i) * X ^ (i : ℕ) + (p : R) • D := by
  choose d hd using fun i => exists_phi_sub_expand_eq_smul p (g i)
  refine ⟨∑ i, d i * X ^ (i : ℕ), ?_⟩
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_mul_assoc, ← hd i]
  ring

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Introduce `hdvd`. Establish `h1 : (p : ℤ) ∣ ((p * n + j - i : ℕ) : ℤ)` using `Int.natCast_dvd_natCast.mpr hdvd`. Move the coercions through the operations in `[Nat.cast_sub hle] at h1`. Establish `h2 : (p : ℤ) ∣ (j : ℤ) - i`. Establish `h3 : (j : ℤ) - i = (p * n + j - i) - p * n` using `by ring`.

Rewrite using `[h3]`. Conclude with `dvd_sub h1 (dvd_mul_right _ _)`. Establish `h4` using `Int.eq_zero_of_abs_lt_dvd h2 (by`. Use `i.isLt` as an intermediate fact. Use `j.isLt` as an intermediate fact.

Apply the tactic sequence `rw [abs_lt]; constructor <;> omega)`. Conclude with `hij (Fin.ext (by omega))`.
-/
private lemma not_dvd_mul_add_sub_of_ne {n : ℕ} {i j : Fin p} (hij : i ≠ j) (hle : (i : ℕ) ≤ p * n + j) :
    ¬ p ∣ p * n + j - i := by
  intro hdvd
  have h1 : (p : ℤ) ∣ ((p * n + j - i : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hdvd
  push_cast [Nat.cast_sub hle] at h1
  have h2 : (p : ℤ) ∣ (j : ℤ) - i := by
    have h3 : (j : ℤ) - i = (p * n + j - i) - p * n := by ring
    rw [h3]
    exact dvd_sub h1 (dvd_mul_right _ _)
  have h4 := Int.eq_zero_of_abs_lt_dvd h2 (by
    have := i.isLt; have := j.isLt
    rw [abs_lt]; constructor <;> omega)
  exact hij (Fin.ext (by omega))

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Rewrite using `[map_sum, Finset.sum_eq_single j]`. Rewrite using `[coeff_mul_X_pow, coeff_expand_mul]`. Introduce `i _ hij`. Rewrite using `[coeff_mul_X_pow']`. Use `split_ifs with hle`.

Conclude with `coeff_expand_of_not_dvd p hp.out.ne_zero _ (not_dvd_mul_add_sub_of_ne p hij hle)`. Both sides reduce to the same expression. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
private lemma coeff_sum_expand_mul_X_pow (g : Fin p → R⟦X⟧) (n : ℕ) (j : Fin p) :
    coeff (p * n + j) (∑ i, expand p hp.out.ne_zero (g i) * X ^ (i : ℕ)) = coeff n (g j) := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [coeff_mul_X_pow, coeff_expand_mul]
  · intro i _ hij
    rw [coeff_mul_X_pow']
    split_ifs with hle
    · exact coeff_expand_of_not_dvd p hp.out.ne_zero _ (not_dvd_mul_add_sub_of_ne p hij hle)
    · rfl
  · intro h; exact absurd (Finset.mem_univ _) h

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Use extensionality with `m`. Establish `hm` using `coeff_sum_expand_mul_X_pow p (fun i : Fin p => PowerSeries.mk fun n => coeff (p * n + i) h) (m / p) ⟨m % p, Nat.mod_lt _ hp.out.pos⟩`. Simplify using `only [Nat.div_add_mod, coeff_mk] at hm`. Rewrite using `[hm]`.
-/
private lemma sum_expand_mk_coeff_mul_X_pow_eq (h : R⟦X⟧) :
    ∑ i : Fin p, expand p hp.out.ne_zero (PowerSeries.mk fun n => coeff (p * n + i) h) * X ^ (i : ℕ) = h := by
  ext m
  have hm := coeff_sum_expand_mul_X_pow p (fun i : Fin p => PowerSeries.mk fun n => coeff (p * n + i) h)
    (m / p) ⟨m % p, Nat.mod_lt _ hp.out.pos⟩
  simp only [Nat.div_add_mod, coeff_mk] at hm
  rw [hm]

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Use extensionality with `n`. Rewrite using `[← coeff_sum_expand_mul_X_pow p g n j, hg, map_zero, map_zero]`.
-/
private lemma eq_zero_of_sum_expand_mul_X_pow_eq_zero (g : Fin p → R⟦X⟧)
    (hg : ∑ i, expand p hp.out.ne_zero (g i) * X ^ (i : ℕ) = 0) (j : Fin p) : g j = 0 := by
  ext n
  rw [← coeff_sum_expand_mul_X_pow p g n j, hg, map_zero, map_zero]

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
variable [IsAdicComplete (Ideal.span {(p : R)}) R] in
/- English proof (translation)
Establish `key : ∀ k : ℕ, ∃ w : Fin p → R⟦X⟧, ∀ i, g i = ((p : R) ^ k) • w i`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => exact ⟨g, fun i => by simp⟩`. Consider the case `succ k ih`.

Take `⟨w, hw⟩` from `ih`. Take `⟨D, hD⟩` from `exists_sum_phi_eq_sum_expand_add_smul p w`. Establish `hψ : ((p : R) ^ k) • ∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (w i) * X ^ (i : ℕ) = 0`. Rewrite using `[← hg, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hw i, map_smul, smul_mul_assoc]`. Rewrite `hψ` using `[hD, smul_add, smul_smul, ← pow_succ]`. Establish `h0 : ∑ i, expand p hp.out.ne_zero (g i + ((p : R) ^ (k + 1)) • PowerSeries.mk fun n => coeff (p * n + i) D) * X ^ (i : ℕ) = 0`. Simplify using `only [map_add, map_smul, add_mul, smul_mul_assoc, Finset.sum_add_distrib, ← Finset.smul_sum, sum_expand_mk_coeff_mul_X_pow_eq, hw]`. Conclude with `hψ`.

Use `⟨fun i => -PowerSeries.mk fun n => coeff (p * n + i) D, fun i => ?_⟩` and prove the remaining obligations. Use `eq_zero_of_sum_expand_mul_X_pow_eq_zero p _ h0 i` as an intermediate fact. Rewrite using `[smul_neg, eq_neg_iff_add_eq_zero]`. Conclude with `this`. Use extensionality with `n`.

Rewrite using `[map_zero]`. Use `IsHausdorff.haus' (I := Ideal.span {(p : R)}) (coeff n (g i)) fun k => ?_` and prove the remaining obligations. Take `⟨w, hw⟩` from `key k`. Rewrite using `[SModEq.sub_mem, sub_zero, hw i, coeff_smul]`. Conclude with `Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top`.
-/
theorem _root_.GlobalTheory.Col.Model.indep (hu : (p : R) ∈ nonunits R) (g : Fin p → PowerSeries R)
    (hg : ∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (g i) * X ^ (i : ℕ) = 0) (i : Fin p) : g i = 0 := by
  have key : ∀ k : ℕ, ∃ w : Fin p → R⟦X⟧, ∀ i, g i = ((p : R) ^ k) • w i := by
    intro k
    induction k with
    | zero => exact ⟨g, fun i => by simp⟩
    | succ k ih =>
      obtain ⟨w, hw⟩ := ih
      obtain ⟨D, hD⟩ := exists_sum_phi_eq_sum_expand_add_smul p w
      have hψ : ((p : R) ^ k) • ∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (w i) * X ^ (i : ℕ) = 0 := by
        rw [← hg, Finset.smul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hw i, map_smul, smul_mul_assoc]
      rw [hD, smul_add, smul_smul, ← pow_succ] at hψ
      have h0 : ∑ i, expand p hp.out.ne_zero
          (g i + ((p : R) ^ (k + 1)) • PowerSeries.mk fun n => coeff (p * n + i) D) * X ^ (i : ℕ) = 0 := by
        simp only [map_add, map_smul, add_mul, smul_mul_assoc, Finset.sum_add_distrib, ← Finset.smul_sum,
          sum_expand_mk_coeff_mul_X_pow_eq, hw]
        exact hψ
      refine ⟨fun i => -PowerSeries.mk fun n => coeff (p * n + i) D, fun i => ?_⟩
      have := eq_zero_of_sum_expand_mul_X_pow_eq_zero p _ h0 i
      rw [smul_neg, eq_neg_iff_add_eq_zero]
      exact this
  ext n
  rw [map_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(p : R)}) (coeff n (g i)) fun k => ?_
  obtain ⟨w, hw⟩ := key k
  rw [SModEq.sub_mem, sub_zero, hw i, coeff_smul]
  exact Submodule.smul_mem_smul (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) k) Submodule.mem_top

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, hc⟩`. Conclude with `⟨c, by rw [← hc, mul_comm]⟩`. Introduce and unpack `⟨c, hc⟩`.

Conclude with `⟨c, by rw [hc, mul_comm]⟩`.
-/
private lemma mem_span_pow_smul_univ_iff_eq_pow_mul (K : ℕ) (x : R) :
    x ∈ ((Ideal.span {(p : R)}) ^ K • ⊤ : Submodule R R) ↔ ∃ c, x = (p : R) ^ K * c := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [← hc, mul_comm]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, by rw [hc, mul_comm]⟩

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] in
variable [IsAdicComplete (Ideal.span {(p : R)}) R] in
/- English proof (translation)
Use `set ψ : (Fin p → R⟦X⟧) → R⟦X⟧ := fun g => ∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (g i) * X ^ (i : ℕ) with hψdef`. Establish `ψ_add : ∀ a b, ψ (a + b) = ψ a + ψ b` using `fun a b => by`. Simplify using `only [hψdef, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]`. Establish `ψ_smul : ∀ (c : R) a, ψ (c • a) = c • ψ a` using `fun c a => by`. Simplify using `only [hψdef, Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum]`.

Establish `ψ_zero : ψ 0 = 0` using `by simp [hψdef]`. Establish `step : ∀ h : R⟦X⟧, ∃ g : Fin p → R⟦X⟧, ∃ h' : R⟦X⟧, h = ψ g + (p : R) • h'`. Introduce `h`. Take `⟨D, hD⟩` from `exists_sum_phi_eq_sum_expand_add_smul p (fun i => PowerSeries.mk fun n => coeff (p * n + i) h)`. Rewrite `hD` using `[sum_expand_mk_coeff_mul_X_pow_eq]`.

Use `⟨fun i => PowerSeries.mk fun n => coeff (p * n + i) h, -D, ?_⟩` and prove the remaining obligations. Simplify using `only [hψdef]`. Rewrite using `[hD, smul_neg]`. Normalize the expressions using the abelian group laws. Use `choose G H hGH using step`.

Set `hs : ℕ → R⟦X⟧` to `fun k => Nat.rec h (fun _ x => H x) k`. Establish `hs_succ : ∀ k, hs (k + 1) = H (hs k)` using `fun k => rfl`. Set `A : ℕ → Fin p → R⟦X⟧` to `fun K => ∑ k ∈ Finset.range K, ((p : R) ^ k) • G (hs k)`. Establish `hA : ∀ K, h = ψ (A K) + ((p : R) ^ K) • hs K`. Introduce `K`.

Proceed by induction on `K with`. Consider the case `zero => show h = ψ (∑ k ∈ Finset.range 0, ((p : R) ^ k) • G (hs k)) + ((p : R) ^ 0) • h`. Rewrite using `[Finset.sum_range_zero, ψ_zero, pow_zero, one_smul, zero_add]`. Consider the case `succ K ih => conv_lhs => rw [ih]`. Rewrite using `[show A (K + 1) = A K + ((p : R) ^ K) • G (hs K) from Finset.sum_range_succ _ _, ψ_add, ψ_smul, hs_succ]`.

Use `conv_lhs => rw [hGH (hs K)]`. Rewrite using `[smul_add, smul_smul, ← pow_succ]`. Normalize the expressions using the abelian group laws. Establish `hcauchy : ∀ (i : Fin p) (n : ℕ) {a b : ℕ}, a ≤ b → coeff n (A a i) ≡ coeff n (A b i) [SMOD ((Ideal.span {(p : R)}) ^ a • ⊤ : Submodule R R)]`. Introduce `i n a b hab`.

Rewrite using `[SModEq.sub_mem, mem_span_pow_smul_univ_iff_eq_pow_mul]`. Establish `hsplit : A b = A a + ∑ k ∈ Finset.Ico a b, ((p : R) ^ k) • G (hs k)`. Simplify using `only [A]`. Rewrite using `[Finset.sum_range_add_sum_Ico _ hab]`. Rewrite using `[hsplit]`.

Simplify using `only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, map_add, map_sum, coeff_smul, smul_eq_mul, sub_add_cancel_left]`. Use `⟨-∑ k ∈ Finset.Ico a b, (p : R) ^ (k - a) * coeff n (G (hs k) i), ?_⟩` and prove the remaining obligations. Rewrite using `[mul_neg, Finset.mul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Rewrite using `[← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.1 hk).1]`. Establish `hlim : ∀ (i : Fin p) (n : ℕ), ∃ L : R, ∀ K, coeff n (A K i) ≡ L [SMOD ((Ideal.span {(p : R)}) ^ K • ⊤ : Submodule R R)]` using `fun i n => IsPrecomplete.prec' _ (hcauchy i n)`. Use `choose L hL using hlim`. Use `⟨fun i => PowerSeries.mk (L i), ?_⟩` and prove the remaining obligations. Use `show h = ψ (fun i => PowerSeries.mk (L i))`.

Rewrite using `[← sub_eq_zero]`. Use extensionality with `m`. Rewrite using `[map_zero]`. Use `IsHausdorff.haus' (I := Ideal.span {(p : R)}) _ fun K => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, mem_span_pow_smul_univ_iff_eq_pow_mul]`.

Establish `hΔ : ∀ (i : Fin p) (n : ℕ), ∃ c, coeff n (A K i) - L i n = (p : R) ^ K * c` using `fun i n => (mem_span_pow_smul_univ_iff_eq_pow_mul p K _).1 (SModEq.sub_mem.1 (hL i n K))`. Use `choose c hc using hΔ`. Establish `hdiff : A K - (fun i => PowerSeries.mk (L i)) = ((p : R) ^ K) • (fun i => PowerSeries.mk (c i))`. Use function extensionality and compare the values at `i`. Use extensionality with `n`.

Simplify using `[hc]`. Establish `e1 : ψ (A K) = ψ (fun i => PowerSeries.mk (L i)) + ((p : R) ^ K) • ψ (fun i => PowerSeries.mk (c i))`. Rewrite using `[← ψ_smul, ← ψ_add, ← hdiff, add_sub_cancel]`. Establish `e2 : h - ψ (fun i => PowerSeries.mk (L i)) = ((p : R) ^ K) • (hs K + ψ (fun i => PowerSeries.mk (c i)))` using `by conv_lhs => rw [hA K]`. Rewrite using `[e1, smul_add]`.

Normalize the expressions using the abelian group laws. Rewrite using `[e2, coeff_smul]`. Conclude with `⟨_, rfl⟩`.
-/
theorem _root_.GlobalTheory.Col.Model.spans (hu : (p : R) ∈ nonunits R) (h : PowerSeries R) :
    ∃ g : Fin p → PowerSeries R, h = ∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (g i) * X ^ (i : ℕ) := by
  set ψ : (Fin p → R⟦X⟧) → R⟦X⟧ := fun g => ∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (g i) * X ^ (i : ℕ)
    with hψdef
  have ψ_add : ∀ a b, ψ (a + b) = ψ a + ψ b := fun a b => by
    simp only [hψdef, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]
  have ψ_smul : ∀ (c : R) a, ψ (c • a) = c • ψ a := fun c a => by
    simp only [hψdef, Pi.smul_apply, map_smul, smul_mul_assoc, Finset.smul_sum]
  have ψ_zero : ψ 0 = 0 := by simp [hψdef]
  have step : ∀ h : R⟦X⟧, ∃ g : Fin p → R⟦X⟧, ∃ h' : R⟦X⟧, h = ψ g + (p : R) • h' := by
    intro h
    obtain ⟨D, hD⟩ := exists_sum_phi_eq_sum_expand_add_smul p (fun i => PowerSeries.mk fun n => coeff (p * n + i) h)
    rw [sum_expand_mk_coeff_mul_X_pow_eq] at hD
    refine ⟨fun i => PowerSeries.mk fun n => coeff (p * n + i) h, -D, ?_⟩
    simp only [hψdef]
    rw [hD, smul_neg]
    abel
  choose G H hGH using step
  let hs : ℕ → R⟦X⟧ := fun k => Nat.rec h (fun _ x => H x) k
  have hs_succ : ∀ k, hs (k + 1) = H (hs k) := fun k => rfl
  let A : ℕ → Fin p → R⟦X⟧ := fun K => ∑ k ∈ Finset.range K, ((p : R) ^ k) • G (hs k)
  have hA : ∀ K, h = ψ (A K) + ((p : R) ^ K) • hs K := by
    intro K
    induction K with
    | zero =>
      show h = ψ (∑ k ∈ Finset.range 0, ((p : R) ^ k) • G (hs k)) + ((p : R) ^ 0) • h
      rw [Finset.sum_range_zero, ψ_zero, pow_zero, one_smul, zero_add]
    | succ K ih =>
      conv_lhs => rw [ih]
      rw [show A (K + 1) = A K + ((p : R) ^ K) • G (hs K) from Finset.sum_range_succ _ _, ψ_add, ψ_smul,
        hs_succ]
      conv_lhs => rw [hGH (hs K)]
      rw [smul_add, smul_smul, ← pow_succ]
      abel
  have hcauchy : ∀ (i : Fin p) (n : ℕ) {a b : ℕ}, a ≤ b →
      coeff n (A a i) ≡ coeff n (A b i) [SMOD ((Ideal.span {(p : R)}) ^ a • ⊤ : Submodule R R)] := by
    intro i n a b hab
    rw [SModEq.sub_mem, mem_span_pow_smul_univ_iff_eq_pow_mul]
    have hsplit : A b = A a + ∑ k ∈ Finset.Ico a b, ((p : R) ^ k) • G (hs k) := by
      simp only [A]
      rw [Finset.sum_range_add_sum_Ico _ hab]
    rw [hsplit]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, map_add, map_sum, coeff_smul, smul_eq_mul,
      sub_add_cancel_left]
    refine ⟨-∑ k ∈ Finset.Ico a b, (p : R) ^ (k - a) * coeff n (G (hs k) i), ?_⟩
    rw [mul_neg, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' (Finset.mem_Ico.1 hk).1]
  have hlim : ∀ (i : Fin p) (n : ℕ), ∃ L : R, ∀ K,
      coeff n (A K i) ≡ L [SMOD ((Ideal.span {(p : R)}) ^ K • ⊤ : Submodule R R)] :=
    fun i n => IsPrecomplete.prec' _ (hcauchy i n)
  choose L hL using hlim
  refine ⟨fun i => PowerSeries.mk (L i), ?_⟩
  show h = ψ (fun i => PowerSeries.mk (L i))
  rw [← sub_eq_zero]
  ext m
  rw [map_zero]
  refine IsHausdorff.haus' (I := Ideal.span {(p : R)}) _ fun K => ?_
  rw [SModEq.sub_mem, sub_zero, mem_span_pow_smul_univ_iff_eq_pow_mul]
  have hΔ : ∀ (i : Fin p) (n : ℕ), ∃ c, coeff n (A K i) - L i n = (p : R) ^ K * c :=
    fun i n => (mem_span_pow_smul_univ_iff_eq_pow_mul p K _).1 (SModEq.sub_mem.1 (hL i n K))
  choose c hc using hΔ
  have hdiff : A K - (fun i => PowerSeries.mk (L i)) = ((p : R) ^ K) • (fun i => PowerSeries.mk (c i)) := by
    funext i
    ext n
    simp [hc]
  have e1 : ψ (A K) = ψ (fun i => PowerSeries.mk (L i)) + ((p : R) ^ K) • ψ (fun i => PowerSeries.mk (c i)) := by
    rw [← ψ_smul, ← ψ_add, ← hdiff, add_sub_cancel]
  have e2 : h - ψ (fun i => PowerSeries.mk (L i)) = ((p : R) ^ K) • (hs K + ψ (fun i => PowerSeries.mk (c i))) := by
    conv_lhs => rw [hA K]
    rw [e1, smul_add]
    abel
  rw [e2, coeff_smul]
  exact ⟨_, rfl⟩

end Free

def Up (R : Type) [CommRing R] (_p : ℕ) : Type := PowerSeries R

instance (R : Type) [CommRing R] (p : ℕ) : CommRing (Up R p) := inferInstanceAs (CommRing (PowerSeries R))

instance (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] : Algebra (PowerSeries R) (Up R p) :=
  RingHom.toAlgebra (S := Up R p) (phi (R := R) p hp.out.pos).toRingHom

section Basis
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem normOp_eq (h : PowerSeries R) : normOp p h = Algebra.norm (PowerSeries R) (S := Up R p) h := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trOp_eq (h : PowerSeries R) : trOp p h = Algebra.trace (PowerSeries R) (Up R p) h := rfl

variable [IsAdicComplete (Ideal.span {(p : R)}) R]

def basis (hu : (p : R) ∈ nonunits R) : Module.Basis (Fin p) (PowerSeries R) (Up R p) :=
  Module.Basis.mk (v := fun i => (show Up R p from (X : PowerSeries R) ^ (i : ℕ)))
    (Fintype.linearIndependent_iff.2 fun g hg i => indep p hu g hg i)
    (fun h _ => by
      obtain ⟨g, hg⟩ := spans p hu h
      rw [Submodule.mem_span_range_iff_exists_fun]
      exact ⟨g, hg.symm⟩)

/- English proof (translation)
Use `Algebra.norm_algebraMap_of_basis (basis p hu) g` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Conclude with `this`.
-/
theorem normOp_phi (hu : (p : R) ∈ nonunits R) (g : PowerSeries R) : normOp p (phi p hp.out.pos g) = g ^ p := by
  have := Algebra.norm_algebraMap_of_basis (basis p hu) g
  rw [Fintype.card_fin] at this
  exact this

/- English proof (translation)
Use `Algebra.trace_algebraMap_of_basis (basis p hu) g` as an intermediate fact. Rewrite `this` using `[Fintype.card_fin]`. Conclude with `this`.
-/
theorem trOp_phi (hu : (p : R) ∈ nonunits R) (g : PowerSeries R) : trOp p (phi p hp.out.pos g) = p • g := by
  have := Algebra.trace_algebraMap_of_basis (basis p hu) g
  rw [Fintype.card_fin] at this
  exact this

end Basis

/- English proof (translation)
Use `haveI := F.complete`. Conclude with `⟨normOp_phi p F.prime.not_isUnit g, trOp_phi p F.prime.not_isUnit g⟩`.
-/
theorem frobLift_ops {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (F : FrobLift R p σ)
    (g : PowerSeries R) : normOp p (phi p hp.out.pos g) = g ^ p ∧ trOp p (phi p hp.out.pos g) = p • g := by
  haveI := F.complete
  exact ⟨normOp_phi p F.prime.not_isUnit g, trOp_phi p F.prime.not_isUnit g⟩

def UpL (R : Type) [CommRing R] (p m : ℕ) (_hm : 1 ≤ m) : Type := lev R p (m + 1)

instance (R : Type) [CommRing R] (p m : ℕ) (hm : 1 ≤ m) : CommRing (UpL R p m hm) := inferInstanceAs (CommRing (lev R p (m + 1)))

instance (R : Type) [CommRing R] (p m : ℕ) [Fact p.Prime] (hm : 1 ≤ m) : Algebra (lev R p m) (UpL R p m hm) :=
  RingHom.toAlgebra (S := UpL R p m hm) (up (R := R) p m hm)

section Level
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : 1 ≤ m)

def toUp (p : ℕ) (h : PowerSeries R) : Up R p := h

def toUpL (p m : ℕ) (hm : 1 ≤ m) (x : lev R p (m + 1)) : UpL R p m hm := x

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem up_ev (g : PowerSeries R) : up p m hm (ev R p m g) = ev R p (m + 1) (phi p hp.out.pos g) := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem nrm_eq (x : lev R p (m + 1)) : nrm p m hm x = Algebra.norm (lev R p m) (S := UpL R p m hm) x := rfl

variable [IsAdicComplete (Ideal.span {(p : R)}) R]

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : 1 ≤ m) in
variable [IsAdicComplete (Ideal.span {(p : R)}) R] in
/- English proof (translation)
Establish `hsurj : Function.Surjective (_root_.GlobalTheory.Col.ev R p m)` using `Ideal.Quotient.mk_surjective`. Use `choose g hg using fun i => hsurj (x i)`. Establish `hzero : _root_.GlobalTheory.Col.ev R p (m + 1) (∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (g i) * X ^ (i : ℕ)) = 0`. Rewrite using `[map_sum, ← hx]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, ← _root_.GlobalTheory.Col.Model.up_ev p m hm, hg]`. Take `⟨k, hk⟩` from `Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hzero)`. Take `⟨d, hd⟩` from `_root_.GlobalTheory.Col.Model.spans p hu k`. Establish `hdiff : ∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (g i - d i * _root_.GlobalTheory.Col.cyc R p m) * X ^ (i : ℕ) = 0`. Simplify using `only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]`.

Rewrite using `[sub_eq_zero, ← hk, hd, Finset.sum_mul, ← _root_.GlobalTheory.Col.phi_cyc p m hm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hgi` using `_root_.GlobalTheory.Col.Model.indep p hu _ hdiff i`. Rewrite `hgi` using `[sub_eq_zero]`.

Rewrite using `[← hg, hgi, map_mul, _root_.GlobalTheory.Col.ev_cyc_self, mul_zero]`.
-/
theorem _root_.GlobalTheory.Col.Model.indepL (hu : (p : R) ∈ nonunits R) (x : Fin p → _root_.GlobalTheory.Col.lev R p m)
    (hx : ∑ i, _root_.GlobalTheory.Col.up p m hm (x i) * _root_.GlobalTheory.Col.ev R p (m + 1) (X ^ (i : ℕ)) = 0) (i : Fin p) : x i = 0 := by
  have hsurj : Function.Surjective (_root_.GlobalTheory.Col.ev R p m) := Ideal.Quotient.mk_surjective
  choose g hg using fun i => hsurj (x i)
  have hzero : _root_.GlobalTheory.Col.ev R p (m + 1)
      (∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos (g i) * X ^ (i : ℕ)) = 0 := by
    rw [map_sum, ← hx]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, ← _root_.GlobalTheory.Col.Model.up_ev p m hm, hg]
  obtain ⟨k, hk⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hzero)
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.Col.Model.spans p hu k
  have hdiff : ∑ i, _root_.GlobalTheory.Col.phi p hp.out.pos
      (g i - d i * _root_.GlobalTheory.Col.cyc R p m) * X ^ (i : ℕ) = 0 := by
    simp only [map_sub, map_mul, sub_mul, Finset.sum_sub_distrib]
    rw [sub_eq_zero, ← hk, hd, Finset.sum_mul, ← _root_.GlobalTheory.Col.phi_cyc p m hm]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hgi := _root_.GlobalTheory.Col.Model.indep p hu _ hdiff i
  rw [sub_eq_zero] at hgi
  rw [← hg, hgi, map_mul, _root_.GlobalTheory.Col.ev_cyc_self, mul_zero]

def basisL (hu : (p : R) ∈ nonunits R) : Module.Basis (Fin p) (lev R p m) (UpL R p m hm) :=
  Module.Basis.mk (v := fun i => toUpL p m hm (ev R p (m + 1) ((X : PowerSeries R) ^ (i : ℕ))))
    (Fintype.linearIndependent_iff.2 fun g hg i => indepL p m hm hu g hg i)
    (fun x _ => by
      obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective (show lev R p (m + 1) from x)
      obtain ⟨g, hg⟩ := spans p hu h
      refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun i => ev R p m (g i), ?_⟩
      change ∑ i, up p m hm (ev R p m (g i)) * ev R p (m + 1) (X ^ (i : ℕ)) = ev R p (m + 1) h
      rw [hg, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_mul, up_ev])

open PowerSeries in
variable {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] (m : ℕ) (hm : 1 ≤ m) in
variable [IsAdicComplete (Ideal.span {(p : R)}) R] in

/- English proof (translation)
Establish `hN1 : _root_.GlobalTheory.Col.normOp p h = Algebra.norm (PowerSeries R) (_root_.GlobalTheory.Col.Model.toUp p h)` using `rfl`. Establish `hN2 : _root_.GlobalTheory.Col.nrm p m hm (_root_.GlobalTheory.Col.ev R p (m + 1) h) = Algebra.norm (_root_.GlobalTheory.Col.lev R p m) (_root_.GlobalTheory.Col.Model.toUpL p m hm (_root_.GlobalTheory.Col.ev R p (m + 1) h))` using `rfl`. Rewrite using `[hN1, hN2, Algebra.norm_eq_matrix_det (_root_.GlobalTheory.Col.Model.basis p hu), Algebra.norm_eq_matrix_det (_root_.GlobalTheory.Col.Model.basisL p m hm hu), RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul]`. Use `set c : Fin p → PowerSeries R := fun k => (_root_.GlobalTheory.Col.Model.basis p hu).repr (_root_.GlobalTheory.Col.Model.toUp p h * _root_.GlobalTheory.Col.Model.basis p hu j) k with hcdef`. Establish `hb : ∀ k : Fin p, _root_.GlobalTheory.Col.Model.basis p hu k = _root_.GlobalTheory.Col.Model.toUp p (X ^ (k : ℕ))` using `fun k => by`. Unfold `_root_.GlobalTheory.Col.Model.basis`. Rewrite using `[Module.Basis.mk_apply]`.

Both sides reduce to the same expression. Establish `hc : _root_.GlobalTheory.Col.Model.toUp p h * _root_.GlobalTheory.Col.Model.basis p hu j = ∑ k, c k • _root_.GlobalTheory.Col.Model.basis p hu k` using `((_root_.GlobalTheory.Col.Model.basis p hu).sum_repr _).symm`. Establish `hc' : h * X ^ (j : ℕ) = ∑ k, _root_.GlobalTheory.Col.phi p hp.out.pos (c k) * X ^ (k : ℕ)`. Simplify using `only [Algebra.smul_def, hb] at hc`. Conclude with `hc`.

Establish `key : _root_.GlobalTheory.Col.Model.toUpL p m hm (_root_.GlobalTheory.Col.ev R p (m + 1) h) * _root_.GlobalTheory.Col.Model.basisL p m hm hu j = ∑ k, _root_.GlobalTheory.Col.ev R p m (c k) • _root_.GlobalTheory.Col.Model.basisL p m hm hu k`. Simplify using `only [_root_.GlobalTheory.Col.Model.basisL, Module.Basis.mk_apply, Algebra.smul_def]`. Express the relevant statement in the definitionally equal form `_root_.GlobalTheory.Col.ev R p (m + 1) h * _root_.GlobalTheory.Col.ev R p (m + 1) (X ^ (j : ℕ)) = ∑ k, _root_.GlobalTheory.Col.up p m hm (_root_.GlobalTheory.Col.ev R p m (c k)) * _root_.GlobalTheory.Col.ev R p (m + 1) (X ^ (k : ℕ))`. Rewrite using `[← map_mul, hc', map_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, _root_.GlobalTheory.Col.Model.up_ev]`. Rewrite using `[key, Module.Basis.repr_sum_self]`.
-/
theorem _root_.GlobalTheory.Col.Model.nrm_ev (hu : (p : R) ∈ nonunits R) (h : PowerSeries R) :
    _root_.GlobalTheory.Col.nrm p m hm (_root_.GlobalTheory.Col.ev R p (m + 1) h) = _root_.GlobalTheory.Col.ev R p m (_root_.GlobalTheory.Col.normOp p h) := by
  have hN1 : _root_.GlobalTheory.Col.normOp p h =
      Algebra.norm (PowerSeries R) (_root_.GlobalTheory.Col.Model.toUp p h) := rfl
  have hN2 : _root_.GlobalTheory.Col.nrm p m hm (_root_.GlobalTheory.Col.ev R p (m + 1) h) =
      Algebra.norm (_root_.GlobalTheory.Col.lev R p m)
        (_root_.GlobalTheory.Col.Model.toUpL p m hm (_root_.GlobalTheory.Col.ev R p (m + 1) h)) := rfl
  rw [hN1, hN2, Algebra.norm_eq_matrix_det (_root_.GlobalTheory.Col.Model.basis p hu),
    Algebra.norm_eq_matrix_det (_root_.GlobalTheory.Col.Model.basisL p m hm hu), RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul,
    Algebra.leftMulMatrix_eq_repr_mul]
  set c : Fin p → PowerSeries R := fun k =>
    (_root_.GlobalTheory.Col.Model.basis p hu).repr
      (_root_.GlobalTheory.Col.Model.toUp p h * _root_.GlobalTheory.Col.Model.basis p hu j) k with hcdef
  have hb : ∀ k : Fin p, _root_.GlobalTheory.Col.Model.basis p hu k =
      _root_.GlobalTheory.Col.Model.toUp p (X ^ (k : ℕ)) := fun k => by
    unfold _root_.GlobalTheory.Col.Model.basis
    rw [Module.Basis.mk_apply]
    rfl
  have hc : _root_.GlobalTheory.Col.Model.toUp p h * _root_.GlobalTheory.Col.Model.basis p hu j =
      ∑ k, c k • _root_.GlobalTheory.Col.Model.basis p hu k :=
    ((_root_.GlobalTheory.Col.Model.basis p hu).sum_repr _).symm
  have hc' : h * X ^ (j : ℕ) =
      ∑ k, _root_.GlobalTheory.Col.phi p hp.out.pos (c k) * X ^ (k : ℕ) := by
    simp only [Algebra.smul_def, hb] at hc
    exact hc
  have key : _root_.GlobalTheory.Col.Model.toUpL p m hm (_root_.GlobalTheory.Col.ev R p (m + 1) h) *
      _root_.GlobalTheory.Col.Model.basisL p m hm hu j =
      ∑ k, _root_.GlobalTheory.Col.ev R p m (c k) • _root_.GlobalTheory.Col.Model.basisL p m hm hu k := by
    simp only [_root_.GlobalTheory.Col.Model.basisL, Module.Basis.mk_apply, Algebra.smul_def]
    change _root_.GlobalTheory.Col.ev R p (m + 1) h * _root_.GlobalTheory.Col.ev R p (m + 1) (X ^ (j : ℕ)) =
      ∑ k, _root_.GlobalTheory.Col.up p m hm (_root_.GlobalTheory.Col.ev R p m (c k)) *
        _root_.GlobalTheory.Col.ev R p (m + 1) (X ^ (k : ℕ))
    rw [← map_mul, hc', map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, _root_.GlobalTheory.Col.Model.up_ev]
  rw [key, Module.Basis.repr_sum_self]

end Level

/- English proof (translation)
Use `Ideal.Quotient.nontrivial_iff.2 ?_` and prove the remaining obligations. Rewrite using `[Ne, Ideal.span_singleton_eq_top, isUnit_iff_constantCoeff]`. Establish `: constantCoeff (cyc R p (m + 1)) = (p : R)`. Unfold `cyc`. Rewrite using `[Polynomial.hom_eval₂]`.

Establish `: (constantCoeff : PowerSeries R →+* R).comp C = RingHom.id R` using `by ext; simp`. Rewrite using `[this]`. Simplify using `[Polynomial.eval₂_id, Polynomial.eval_one_cyclotomic_prime_pow]`. Rewrite using `[this]`. Conclude with `hu`.
-/
theorem lev_nontrivial {R : Type} [CommRing R] (p : ℕ) [hp : Fact p.Prime] (hu : (p : R) ∈ nonunits R) (m : ℕ) :
    Nontrivial (lev R p (m + 1)) := by
  refine Ideal.Quotient.nontrivial_iff.2 ?_
  rw [Ne, Ideal.span_singleton_eq_top, isUnit_iff_constantCoeff]
  have : constantCoeff (cyc R p (m + 1)) = (p : R) := by
    unfold cyc
    rw [Polynomial.hom_eval₂]
    have : (constantCoeff : PowerSeries R →+* R).comp C = RingHom.id R := by ext; simp
    rw [this]
    simp [Polynomial.eval₂_id, Polynomial.eval_one_cyclotomic_prime_pow]
  rw [this]; exact hu

/- English proof (translation)
Establish `h1 : dd (1 + X : PowerSeries R) = 1 + X` using `by simp [dd]`. Rewrite using `[h1, phi_one_add_X]`. Take `⟨n, rfl⟩ : ∃ n, p = n + 1` from `⟨p - 1, by omega⟩`. Simplify using `[dd, Derivation.leibniz_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dd_test {R : Type} [CommRing R] (p : ℕ) (hp : 0 < p) :
    dd (phi (R := R) p hp (1 + X)) = (p : PowerSeries R) * phi (R := R) p hp (dd (1 + X : PowerSeries R)) := by
  have h1 : dd (1 + X : PowerSeries R) = 1 + X := by simp [dd]
  rw [h1, phi_one_add_X]
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  simp [dd, Derivation.leibniz_pow]
  ring

end GlobalTheory.Col.Model
