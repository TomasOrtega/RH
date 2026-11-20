import Mathlib
import GroundTheory.PAdicHodge.GaloisOnCp
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Polynomial

noncomputable section

/- English proof (translation)
Establish `hlog : Nat.log p d = k` using `Nat.log_eq_of_pow_le_of_lt_pow h1 h2`. Establish `hv : padicValNat p (Nat.choose d (p ^ k)) = 0`. Rewrite using `[padicValNat_choose h1 (b := k + 1) (by omega), Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ico]`.

Establish `hdvd : p ^ i ∣ p ^ k` using `pow_dvd_pow p (by omega)`. Rewrite using `[Nat.mod_eq_zero_of_dvd hdvd, zero_add, not_le]`. Conclude with `Nat.mod_lt _ (pow_pos hp.out.pos i)`. Establish `hne : Nat.choose d (p ^ k) ≠ 0` using `(Nat.choose_pos h1).ne'`. Break down `(padicValNat.eq_zero_iff.1 hv) with h | h | h` into its components or cases.

Conclude with `absurd h hp.out.one_lt.ne'`. Conclude with `absurd h hne`. Conclude with `h`.
-/
theorem not_dvd_choose_pow_of_lt {p : ℕ} [hp : Fact p.Prime] {d k : ℕ} (h1 : p ^ k ≤ d)
    (h2 : d < p ^ (k + 1)) : ¬ p ∣ Nat.choose d (p ^ k) := by
  have hlog : Nat.log p d = k := Nat.log_eq_of_pow_le_of_lt_pow h1 h2
  have hv : padicValNat p (Nat.choose d (p ^ k)) = 0 := by
    rw [padicValNat_choose h1 (b := k + 1) (by omega), Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hdvd : p ^ i ∣ p ^ k := pow_dvd_pow p (by omega)
    rw [Nat.mod_eq_zero_of_dvd hdvd, zero_add, not_le]
    exact Nat.mod_lt _ (pow_pos hp.out.pos i)
  have hne : Nat.choose d (p ^ k) ≠ 0 := (Nat.choose_pos h1).ne'
  rcases (padicValNat.eq_zero_iff.1 hv) with h | h | h
  · exact absurd h hp.out.one_lt.ne'
  · exact absurd h hne
  · exact h

/- English proof (translation)
Establish `hp1` using `hp.out.one_lt`. Establish `hle : p ^ (k - 1) ≤ p ^ k` using `Nat.pow_le_pow_right hp.out.pos (by omega)`. Establish `hlog : Nat.log p (p ^ k) = k` using `Nat.log_pow hp1 k`. Establish `hsub : p ^ k - p ^ (k - 1) = p ^ (k - 1) * (p - 1)`. Take `⟨j, rfl⟩ : ∃ j, k = j + 1` from `⟨k - 1, by omega⟩`.

Simplify using `only [Nat.add_sub_cancel, pow_succ, Nat.mul_sub, mul_one]`. Establish `hv : padicValNat p (Nat.choose (p ^ k) (p ^ (k - 1))) ≤ 1`. Rewrite using `[padicValNat_choose hle (b := k + 1) (by omega)]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.card_le_card fun i hi => ?_` and prove the remaining obligations.

Rewrite `hi` using `[Finset.mem_filter, Finset.mem_Ico]`. Rewrite using `[Finset.mem_singleton]`. Assume the negation of the conclusion as `hik`. Take `⟨⟨hi1, hi2⟩, hi3⟩` from `hi`. Establish `hik' : i ≤ k - 1` using `by omega`.

Establish `h1 : p ^ (k - 1) % p ^ i = 0` using `Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hik')`. Establish `h2 : (p ^ k - p ^ (k - 1)) % p ^ i = 0`. Rewrite using `[hsub]`. Conclude with `Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (pow_dvd_pow p hik') _)`. Rewrite `hi3` using `[h1, h2]`.

Establish `: 0 < p ^ i` using `pow_pos hp.out.pos i`. Use linear arithmetic over natural numbers and integers. Use `_ = 1 := Finset.card_singleton k`. Introduce `hdvd`. Establish `hne : Nat.choose (p ^ k) (p ^ (k - 1)) ≠ 0` using `(Nat.choose_pos hle).ne'`.

Use `(padicValNat_dvd_iff_le hne).1 hdvd` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem not_sq_dvd_choose_pow_pow {p : ℕ} [hp : Fact p.Prime] {k : ℕ} (hk : 1 ≤ k) :
    ¬ p ^ 2 ∣ Nat.choose (p ^ k) (p ^ (k - 1)) := by
  have hp1 := hp.out.one_lt
  have hle : p ^ (k - 1) ≤ p ^ k := Nat.pow_le_pow_right hp.out.pos (by omega)
  have hlog : Nat.log p (p ^ k) = k := Nat.log_pow hp1 k
  have hsub : p ^ k - p ^ (k - 1) = p ^ (k - 1) * (p - 1) := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, pow_succ, Nat.mul_sub, mul_one]
  have hv : padicValNat p (Nat.choose (p ^ k) (p ^ (k - 1))) ≤ 1 := by
    rw [padicValNat_choose hle (b := k + 1) (by omega)]
    calc _ ≤ ({k} : Finset ℕ).card := by
          refine Finset.card_le_card fun i hi => ?_
          rw [Finset.mem_filter, Finset.mem_Ico] at hi
          rw [Finset.mem_singleton]
          by_contra hik
          obtain ⟨⟨hi1, hi2⟩, hi3⟩ := hi
          have hik' : i ≤ k - 1 := by omega
          have h1 : p ^ (k - 1) % p ^ i = 0 := Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hik')
          have h2 : (p ^ k - p ^ (k - 1)) % p ^ i = 0 := by
            rw [hsub]; exact Nat.mod_eq_zero_of_dvd (Dvd.dvd.mul_right (pow_dvd_pow p hik') _)
          rw [h1, h2] at hi3
          have : 0 < p ^ i := pow_pos hp.out.pos i
          omega
      _ = 1 := Finset.card_singleton k
  intro hdvd
  have hne : Nat.choose (p ^ k) (p ^ (k - 1)) ≠ 0 := (Nat.choose_pos hle).ne'
  have := (padicValNat_dvd_iff_le hne).1 hdvd
  omega

section Norms

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Establish `h1 : (n : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((n : ℚ) : ℚ_[p])`. Rewrite using `[Rat.cast_natCast, map_natCast]`. Rewrite using `[h1]`. Use `(PadicAlgCl.norm_extends p _).trans ?_` and prove the remaining obligations. Rewrite using `[Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn), padicValRat.of_nat]`.

Use `push_cast`. Both sides reduce to the same expression.
-/
theorem norm_natCast_padicAlgCl {n : ℕ} (hn : n ≠ 0) :
    ‖(n : PadicAlgCl p)‖ = (p : ℝ) ^ (-(padicValNat p n : ℤ)) := by
  have h1 : (n : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((n : ℚ) : ℚ_[p]) := by
    rw [Rat.cast_natCast, map_natCast]
  rw [h1]
  refine (PadicAlgCl.norm_extends p _).trans ?_
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast hn),
    padicValRat.of_nat]
  push_cast
  rfl

/- English proof (translation)
Establish `hn : n ≠ 0` using `by rintro rfl; exact h (dvd_zero p)`. Rewrite using `[norm_natCast_padicAlgCl hn, padicValNat.eq_zero_of_not_dvd h]`. Simplify using the standard rewrite rules.
-/
theorem norm_natCast_padicAlgCl_of_not_dvd {n : ℕ} (h : ¬ p ∣ n) :
    ‖(n : PadicAlgCl p)‖ = 1 := by
  have hn : n ≠ 0 := by rintro rfl; exact h (dvd_zero p)
  rw [norm_natCast_padicAlgCl hn, padicValNat.eq_zero_of_not_dvd h]
  simp

/- English proof (translation)
Establish `hv : padicValNat p n ≤ 1`. Assume the negation of the conclusion as `hv`. Conclude with `h ((pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd)`. Rewrite using `[norm_natCast_padicAlgCl hn, ← zpow_neg_one]`. Establish `hp1 : (1 : ℝ) ≤ p` using `by exact_mod_cast hp.out.one_lt.le`.

Conclude with `zpow_le_zpow_right₀ hp1 (by omega)`.
-/
theorem inv_le_norm_natCast_padicAlgCl {n : ℕ} (hn : n ≠ 0) (h : ¬ p ^ 2 ∣ n) :
    (p : ℝ)⁻¹ ≤ ‖(n : PadicAlgCl p)‖ := by
  have hv : padicValNat p n ≤ 1 := by
    by_contra hv
    exact h ((pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd)
  rw [norm_natCast_padicAlgCl hn, ← zpow_neg_one]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  exact zpow_le_zpow_right₀ hp1 (by omega)

end Norms

section Ultra

variable {E : Type*} [NormedField E] [IsUltrametricDist E]

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simpa using hC`. Consider the case `cons a t ih`. Rewrite using `[Multiset.sum_cons]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le (h a (Multiset.mem_cons_self a t)) (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)))`.
-/
theorem norm_multiset_sum_le_of_forall_le {s : Multiset E} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a ∈ s, ‖a‖ ≤ C) : ‖s.sum‖ ≤ C := by
  induction s using Multiset.induction_on with
  | empty => simpa using hC
  | cons a t ih =>
    rw [Multiset.sum_cons]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans
      (max_le (h a (Multiset.mem_cons_self a t))
        (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)))

omit [IsUltrametricDist E] in

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a t ih`. Rewrite using `[Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm (C ^ _)]`. Conclude with `mul_le_mul (h a (Multiset.mem_cons_self a t)) (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)) (norm_nonneg _) ((norm_nonneg a).trans (h a (Multiset.mem_cons_self a t)))`.
-/
theorem norm_multiset_prod_le_pow_card {s : Multiset E} {C : ℝ} (h : ∀ a ∈ s, ‖a‖ ≤ C) :
    ‖s.prod‖ ≤ C ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.prod_cons, norm_mul, Multiset.card_cons, pow_succ, mul_comm (C ^ _)]
    exact mul_le_mul (h a (Multiset.mem_cons_self a t))
      (ih fun b hb => h b (Multiset.mem_cons_of_mem hb)) (norm_nonneg _)
      ((norm_nonneg a).trans (h a (Multiset.mem_cons_self a t)))

omit [IsUltrametricDist E] in

/- English proof (translation)
Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a t ih => rw [Multiset.prod_cons, norm_mul, ih, Multiset.map_cons, Multiset.prod_cons]`.
-/
theorem norm_multiset_prod_eq (s : Multiset E) : ‖s.prod‖ = (s.map norm).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih => rw [Multiset.prod_cons, norm_mul, ih, Multiset.map_cons, Multiset.prod_cons]

/- English proof (translation)
Rewrite using `[Multiset.esymm]`. Use `norm_multiset_sum_le_of_forall_le (pow_nonneg hC j) fun a ha => ?_` and prove the remaining obligations. Take `⟨t, ht, rfl⟩` from `Multiset.mem_map.1 ha`. Rewrite `ht` using `[Multiset.mem_powersetCard]`. Rewrite using `[← ht.2]`.

Conclude with `norm_multiset_prod_le_pow_card fun b hb => h b (Multiset.subset_of_le ht.1 hb)`.
-/
theorem norm_esymm_le {s : Multiset E} {C : ℝ} (hC : 0 ≤ C) (h : ∀ a ∈ s, ‖a‖ ≤ C) (j : ℕ) :
    ‖s.esymm j‖ ≤ C ^ j := by
  rw [Multiset.esymm]
  refine norm_multiset_sum_le_of_forall_le (pow_nonneg hC j) fun a ha => ?_
  obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 ha
  rw [Multiset.mem_powersetCard] at ht
  rw [← ht.2]
  exact norm_multiset_prod_le_pow_card fun b hb => h b (Multiset.subset_of_le ht.1 hb)

/- English proof (translation)
Take `⟨i, hi, hmin⟩` from `Multiset.exists_min_image f hs`. Use `⟨i, hi, le_trans ?_ h⟩` and prove the remaining obligations. Establish `key : ∀ t : Multiset ι, t ≤ s → f i ^ Multiset.card t ≤ (t.map f).prod`. Introduce `t`. Proceed by induction on `t using Multiset.induction_on with`.

Consider the case `empty => simp`. Consider the case `cons a t ih`. Introduce `hts`. Establish `ha : a ∈ s` using `Multiset.mem_of_le hts (Multiset.mem_cons_self a t)`. Rewrite using `[Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]`.

Use `mul_le_mul (hmin a ha) (ih ((Multiset.le_cons_self t a).trans hts)) (pow_nonneg (hf i hi) _) (hf a ha)` and prove the remaining obligations. Conclude with `key s le_rfl`.
-/
theorem exists_pow_card_le_of_prod_le {ι : Type*} {s : Multiset ι} (hs : s ≠ 0) {f : ι → ℝ}
    (hf : ∀ i ∈ s, 0 ≤ f i) {B : ℝ} (h : (s.map f).prod ≤ B) :
    ∃ i ∈ s, f i ^ Multiset.card s ≤ B := by
  obtain ⟨i, hi, hmin⟩ := Multiset.exists_min_image f hs
  refine ⟨i, hi, le_trans ?_ h⟩
  have key : ∀ t : Multiset ι, t ≤ s → f i ^ Multiset.card t ≤ (t.map f).prod := by
    intro t
    induction t using Multiset.induction_on with
    | empty => simp
    | cons a t ih =>
      intro hts
      have ha : a ∈ s := Multiset.mem_of_le hts (Multiset.mem_cons_self a t)
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, pow_succ, mul_comm]
      refine mul_le_mul (hmin a ha) (ih ((Multiset.le_cons_self t a).trans hts))
        (pow_nonneg (hf i hi) _) (hf a ha)
  exact key s le_rfl

end Ultra

section Key

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Establish `hx : IsIntegral K x` using `Algebra.IsIntegral.isIntegral x`. Establish `ha' : aeval a (minpoly K x) = 0`. Rewrite `ha` using `[mem_roots_map (minpoly.ne_zero hx)]`. Rewrite using `[aeval_def]` and apply the resulting hypothesis. Establish `he : minpoly K a = minpoly K x` using `(minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) ha' (minpoly.monic hx)).symm`.

Take `⟨σ, hσ⟩` from `(Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).1 he`. Conclude with `⟨σ, hσ⟩`.
-/
theorem exists_gal_apply_eq_of_mem_roots {x a : PadicAlgCl p}
    (ha : a ∈ ((minpoly K x).map (algebraMap K (PadicAlgCl p))).roots) :
    ∃ σ : Gal(PadicAlgCl p/K), σ x = a := by
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have ha' : aeval a (minpoly K x) = 0 := by
    rw [mem_roots_map (minpoly.ne_zero hx)] at ha
    rwa [aeval_def]
  have he : minpoly K a = minpoly K x :=
    (minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) ha' (minpoly.monic hx)).symm
  obtain ⟨σ, hσ⟩ := (Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).1 he
  exact ⟨σ, hσ⟩

/- English proof (translation)
Use extensionality with `n`. Rewrite using `[hasseDeriv_coeff, coeff_map, coeff_map, hasseDeriv_coeff, map_mul, map_natCast]`.
-/
theorem hasseDeriv_map {R S : Type*} [Semiring R] [Semiring S] (f : R →+* S) (q : ℕ)
    (P : R[X]) : hasseDeriv q (P.map f) = (hasseDeriv q P).map f := by
  ext n
  rw [hasseDeriv_coeff, coeff_map, coeff_map, hasseDeriv_coeff, map_mul, map_natCast]

/- English proof (translation)
Establish `hx : IsIntegral K x` using `Algebra.IsIntegral.isIntegral x`. Use `set P := minpoly K x with hP`. Use `set d := P.natDegree with hd`. Use `set f := algebraMap K (PadicAlgCl p) with hf`. Establish `hρ0 : 0 ≤ ρ` using `by simpa using hρ 1`.

Establish `hPm : (P.map f).Monic` using `(minpoly.monic hx).map f`. Establish `hdm : (P.map f).natDegree = d` using `natDegree_map f`. Establish `hroots : Multiset.card (P.map f).roots = d`. Rewrite using `[IsAlgClosed.card_roots_eq_natDegree, hdm]`. Establish `hsplit : ((P.map f).roots.map fun a => X - C a).prod = P.map f` using `prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm (by rw [hroots, hdm])`.

Use `set Q := hasseDeriv q P with hQ`. Establish `hQm : hasseDeriv q (P.map f) = Q.map f` using `hasseDeriv_map f q P`. Establish `htaylor : taylor x (P.map f) = ((P.map f).roots.map fun a => X + C (x - a)).prod`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_multiset_prod, Multiset.map_map]`.

Use `congr 1`. Use `Multiset.map_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Function.comp_apply]`. Express the relevant statement in the definitionally equal form `taylor x (X - C a) = _`. Rewrite using `[map_sub, taylor_X, taylor_C, C_sub]`.

Expand and normalize the polynomial expressions, which then agree. Establish `heval : (Q.map f).eval x = ((P.map f).roots.map fun a => x - a).esymm (d - q)`. Rewrite using `[← hQm, ← taylor_coeff, htaylor, Multiset.prod_X_add_C_coeff' _ (fun a => x - a) (by rw [hroots]; exact hq.le), hroots]`. Establish `hevalle : ‖(Q.map f).eval x‖ ≤ ρ ^ (d - q)`. Rewrite using `[heval]`.

Use `norm_esymm_le hρ0 (fun c hc => ?_) _` and prove the remaining obligations. Take `⟨a, ha, rfl⟩` from `Multiset.mem_map.1 hc`. Take `⟨σ, rfl⟩` from `exists_gal_apply_eq_of_mem_roots ha`. Rewrite using `[norm_sub_rev]`. Conclude with `hρ σ`.

Establish `hQdeg : (Q.map f).natDegree = d - q`. Rewrite using `[← hQm, natDegree_hasseDeriv, hdm]`. Establish `hQlc : (Q.map f).leadingCoeff = ((Nat.choose d q : ℕ) : PadicAlgCl p)`. Rewrite using `[leadingCoeff, hQdeg, ← hQm, hasseDeriv_coeff, Nat.sub_add_cancel hq.le, ← hdm, ← leadingCoeff, hPm.leadingCoeff, mul_one]`. Establish `hlc0 : ((Nat.choose d q : ℕ) : PadicAlgCl p) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.choose_pos hq.le).ne'`.

Establish `hQcard : Multiset.card (Q.map f).roots = (Q.map f).natDegree` using `IsAlgClosed.card_roots_eq_natDegree`. Establish `hQfac` using `C_leadingCoeff_mul_prod_multiset_X_sub_C hQcard`. Establish `hQeval : (Q.map f).eval x = ((Nat.choose d q : ℕ) : PadicAlgCl p) * ((Q.map f).roots.map fun b => x - b).prod` using `by conv_lhs => rw [← hQfac]`. Rewrite using `[eval_mul, eval_C, hQlc, eval_multiset_prod, Multiset.map_map]`. Use `congr 2`.

Use `Multiset.map_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hne : (Q.map f).roots ≠ 0`. Introduce `h0`. Use `hQcard` as an intermediate fact.

Rewrite `this` using `[h0, hQdeg]`. Simplify using `at this`. Use linear arithmetic over natural numbers and integers. Establish `hprod : ((Q.map f).roots.map fun b => ‖x - b‖).prod ≤ ρ ^ (d - q) / ‖((Nat.choose d q : ℕ) : PadicAlgCl p)‖`. Rewrite using `[le_div_iff₀ (norm_pos_iff.2 hlc0), mul_comm]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hQeval, norm_mul, norm_multiset_prod_eq, Multiset.map_map]`. Both sides reduce to the same expression. Use `_ ≤ ρ ^ (d - q) := hevalle`. Take `⟨b, hb, hble⟩` from `exists_pow_card_le_of_prod_le hne (fun _ _ => norm_nonneg _) hprod`.

Rewrite `hble` using `[hQcard, hQdeg, le_div_iff₀ (norm_pos_iff.2 hlc0), mul_comm]`. Use `⟨b, ?_, hble⟩` and prove the remaining obligations. Establish `hQ0 : Q ≠ 0`. Introduce and unpack `h0`. Rewrite `hne` using `[h0, Polynomial.map_zero, roots_zero]`.

Conclude with `hne rfl`. Establish `hbQ : aeval b Q = 0`. Rewrite `hb` using `[mem_roots_map hQ0]`. Rewrite using `[aeval_def]` and apply the resulting hypothesis. Use `natDegree_le_of_dvd (minpoly.dvd K b hbQ) hQ0` as an intermediate fact.

Rewrite `this` using `[hQ, natDegree_hasseDeriv]`. Conclude with `this`.
-/
theorem exists_close_of_hasseDeriv (x : PadicAlgCl p) {ρ : ℝ}
    (hρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ ρ) {q : ℕ}
    (hq : q < (minpoly K x).natDegree) :
    ∃ b : PadicAlgCl p, (minpoly K b).natDegree ≤ (minpoly K x).natDegree - q ∧
      ‖((Nat.choose (minpoly K x).natDegree q : ℕ) : PadicAlgCl p)‖ *
        ‖x - b‖ ^ ((minpoly K x).natDegree - q) ≤ ρ ^ ((minpoly K x).natDegree - q) := by
  classical
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  set P := minpoly K x with hP
  set d := P.natDegree with hd
  set f := algebraMap K (PadicAlgCl p) with hf
  have hρ0 : 0 ≤ ρ := by simpa using hρ 1
  have hPm : (P.map f).Monic := (minpoly.monic hx).map f
  have hdm : (P.map f).natDegree = d := natDegree_map f
  have hroots : Multiset.card (P.map f).roots = d := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hdm]
  have hsplit : ((P.map f).roots.map fun a => X - C a).prod = P.map f :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm (by rw [hroots, hdm])
  set Q := hasseDeriv q P with hQ
  have hQm : hasseDeriv q (P.map f) = Q.map f := hasseDeriv_map f q P

  have htaylor : taylor x (P.map f) = ((P.map f).roots.map fun a => X + C (x - a)).prod := by
    calc taylor x (P.map f) = taylorAlgHom x (P.map f) := rfl
      _ = _ := by
        conv_lhs => rw [← hsplit]
        rw [map_multiset_prod, Multiset.map_map]
        congr 1
        refine Multiset.map_congr rfl fun a _ => ?_
        rw [Function.comp_apply]
        change taylor x (X - C a) = _
        rw [map_sub, taylor_X, taylor_C, C_sub]
        ring
  have heval : (Q.map f).eval x = ((P.map f).roots.map fun a => x - a).esymm (d - q) := by
    rw [← hQm, ← taylor_coeff, htaylor, Multiset.prod_X_add_C_coeff' _ (fun a => x - a)
      (by rw [hroots]; exact hq.le), hroots]
  have hevalle : ‖(Q.map f).eval x‖ ≤ ρ ^ (d - q) := by
    rw [heval]
    refine norm_esymm_le hρ0 (fun c hc => ?_) _
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hc
    obtain ⟨σ, rfl⟩ := exists_gal_apply_eq_of_mem_roots ha
    rw [norm_sub_rev]
    exact hρ σ

  have hQdeg : (Q.map f).natDegree = d - q := by
    rw [← hQm, natDegree_hasseDeriv, hdm]
  have hQlc : (Q.map f).leadingCoeff = ((Nat.choose d q : ℕ) : PadicAlgCl p) := by
    rw [leadingCoeff, hQdeg, ← hQm, hasseDeriv_coeff, Nat.sub_add_cancel hq.le, ← hdm,
      ← leadingCoeff, hPm.leadingCoeff, mul_one]
  have hlc0 : ((Nat.choose d q : ℕ) : PadicAlgCl p) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.choose_pos hq.le).ne'
  have hQcard : Multiset.card (Q.map f).roots = (Q.map f).natDegree :=
    IsAlgClosed.card_roots_eq_natDegree
  have hQfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hQcard
  have hQeval : (Q.map f).eval x =
      ((Nat.choose d q : ℕ) : PadicAlgCl p) * ((Q.map f).roots.map fun b => x - b).prod := by
    conv_lhs => rw [← hQfac]
    rw [eval_mul, eval_C, hQlc, eval_multiset_prod, Multiset.map_map]
    congr 2
    refine Multiset.map_congr rfl fun b _ => ?_
    simp
  have hne : (Q.map f).roots ≠ 0 := by
    intro h0
    have := hQcard
    rw [h0, hQdeg] at this
    simp at this
    omega
  have hprod : ((Q.map f).roots.map fun b => ‖x - b‖).prod ≤
      ρ ^ (d - q) / ‖((Nat.choose d q : ℕ) : PadicAlgCl p)‖ := by
    rw [le_div_iff₀ (norm_pos_iff.2 hlc0), mul_comm]
    calc ‖((Nat.choose d q : ℕ) : PadicAlgCl p)‖ * ((Q.map f).roots.map fun b => ‖x - b‖).prod
        = ‖(Q.map f).eval x‖ := by
          rw [hQeval, norm_mul, norm_multiset_prod_eq, Multiset.map_map]
          rfl
      _ ≤ ρ ^ (d - q) := hevalle
  obtain ⟨b, hb, hble⟩ := exists_pow_card_le_of_prod_le hne (fun _ _ => norm_nonneg _) hprod
  rw [hQcard, hQdeg, le_div_iff₀ (norm_pos_iff.2 hlc0), mul_comm] at hble
  refine ⟨b, ?_, hble⟩

  have hQ0 : Q ≠ 0 := by
    rintro h0
    rw [h0, Polynomial.map_zero, roots_zero] at hne
    exact hne rfl
  have hbQ : aeval b Q = 0 := by
    rw [mem_roots_map hQ0] at hb
    rwa [aeval_def]
  have := natDegree_le_of_dvd (minpoly.dvd K b hbQ) hQ0
  rw [hQ, natDegree_hasseDeriv] at this
  exact this

/- English proof (translation)
Establish `h1 : σ b - b = (σ (b - x) + (σ x - x)) + (x - b)` using `by rw [map_sub]; ring`. Establish `h2 : ‖σ (b - x)‖ = ‖x - b‖` using `by rw [norm_gal_apply, norm_sub_rev]`. Rewrite using `[h1]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (le_max_left _ _))` and prove the remaining obligations. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Rewrite using `[h2]`. Conclude with `le_max_left _ _`. Conclude with `(hρ σ).trans (le_max_right _ _)`.
-/
theorem norm_gal_apply_sub_le (x b : PadicAlgCl p) {ρ : ℝ}
    (hρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ ρ) (σ : Gal(PadicAlgCl p/K)) :
    ‖σ b - b‖ ≤ max ‖x - b‖ ρ := by
  have h1 : σ b - b = (σ (b - x) + (σ x - x)) + (x - b) := by rw [map_sub]; ring
  have h2 : ‖σ (b - x)‖ = ‖x - b‖ := by rw [norm_gal_apply, norm_sub_rev]
  rw [h1]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (le_max_left _ _))
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
  · rw [h2]; exact le_max_left _ _
  · exact (hρ σ).trans (le_max_right _ _)

end Key

section Induction

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

def axExponent (p k : ℕ) : ℝ := (p : ℝ) / ((p : ℝ) - 1) ^ 2 * (1 - ((p : ℝ) ^ k)⁻¹)

/- English proof (translation)
Conclude with `hp.out.one_lt` after adjusting the coercions.
-/
theorem one_lt_prime_cast : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt

omit hp in

/- English proof (translation)
Simplify using `[axExponent]`.
-/
theorem axExponent_zero : axExponent p 0 = 0 := by simp [axExponent]

/- English proof (translation)
Establish `h1` using `one_lt_prime_cast (p := p)`. Establish `h2 : (p : ℝ) - 1 ≠ 0` using `by linarith`. Establish `h3 : (p : ℝ) ^ k ≠ 0` using `pow_ne_zero _ (by linarith)`. Establish `h4 : (p : ℝ) ≠ 0` using `by linarith`. Simplify using `only [axExponent, pow_succ]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem axExponent_succ (k : ℕ) :
    axExponent p (k + 1) = axExponent p k + 1 / ((p : ℝ) ^ k * ((p : ℝ) - 1)) := by
  have h1 := one_lt_prime_cast (p := p)
  have h2 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (p : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by linarith)
  have h4 : (p : ℝ) ≠ 0 := by linarith
  simp only [axExponent, pow_succ]
  field_simp
  ring

/- English proof (translation)
Establish `h1` using `one_lt_prime_cast (p := p)`. Establish `hC : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2` using `div_nonneg (by linarith) (sq_nonneg _)`. Establish `h2 : 0 ≤ ((p : ℝ) ^ k)⁻¹` using `inv_nonneg.2 (pow_nonneg (by linarith) _)`. Unfold `axExponent`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem axExponent_le (k : ℕ) : axExponent p k ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := by
  have h1 := one_lt_prime_cast (p := p)
  have hC : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  have h2 : 0 ≤ ((p : ℝ) ^ k)⁻¹ := inv_nonneg.2 (pow_nonneg (by linarith) _)
  unfold axExponent
  nlinarith

/- English proof (translation)
Establish `h1` using `one_lt_prime_cast (p := p)`. Establish `hC : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2` using `div_nonneg (by linarith) (sq_nonneg _)`. Establish `h2 : ((p : ℝ) ^ k)⁻¹ ≤ ((p : ℝ) ^ j)⁻¹` using `inv_anti₀ (pow_pos (by linarith) _) (pow_le_pow_right₀ h1.le h)`. Unfold `axExponent`. Conclude with `mul_le_mul_of_nonneg_left (by linarith) hC`.
-/
theorem axExponent_mono {j k : ℕ} (h : j ≤ k) : axExponent p j ≤ axExponent p k := by
  have h1 := one_lt_prime_cast (p := p)
  have hC : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) ^ 2 := div_nonneg (by linarith) (sq_nonneg _)
  have h2 : ((p : ℝ) ^ k)⁻¹ ≤ ((p : ℝ) ^ j)⁻¹ :=
    inv_anti₀ (pow_pos (by linarith) _) (pow_le_pow_right₀ h1.le h)
  unfold axExponent
  exact mul_le_mul_of_nonneg_left (by linarith) hC

/- English proof (translation)
Rewrite using `[← axExponent_zero (p := p)]`. Conclude with `axExponent_mono (Nat.zero_le k)`.
-/
theorem axExponent_nonneg (k : ℕ) : 0 ≤ axExponent p k := by
  rw [← axExponent_zero (p := p)]
  exact axExponent_mono (Nat.zero_le k)

/- English proof (translation)
The claim follows from `Real.one_le_rpow one_lt_prime_cast.le (axExponent_nonneg k)`.
-/
theorem one_le_rpow_axExponent (k : ℕ) : 1 ≤ (p : ℝ) ^ axExponent p k :=
  Real.one_le_rpow one_lt_prime_cast.le (axExponent_nonneg k)

/- English proof (translation)
The claim follows from `Real.rpow_le_rpow_of_exponent_le one_lt_prime_cast.le (axExponent_mono h)`.
-/
theorem rpow_axExponent_mono {j k : ℕ} (h : j ≤ k) :
    (p : ℝ) ^ axExponent p j ≤ (p : ℝ) ^ axExponent p k :=
  Real.rpow_le_rpow_of_exponent_le one_lt_prime_cast.le (axExponent_mono h)

/- English proof (translation)
Rewrite using `[← sub_add_sub_cancel x b y]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h1 h2)`.
-/
theorem norm_sub_le_max_of_le {x b y : PadicAlgCl p} {s t : ℝ} (h1 : ‖x - b‖ ≤ s)
    (h2 : ‖b - y‖ ≤ t) : ‖x - y‖ ≤ max s t := by
  rw [← sub_add_sub_cancel x b y]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max h1 h2)

/- English proof (translation)
Proceed by induction on `d using Nat.strong_induction_on with`. Consider the case `_ d IH`. Introduce `x hxd ρ hρ`. Establish `hx : IsIntegral K x` using `Algebra.IsIntegral.isIntegral x`. Establish `hρ0 : 0 ≤ ρ` using `by simpa using hρ 1`.

Establish `hp1` using `one_lt_prime_cast (p := p)`. Establish `hdpos : 0 < d` using `hxd ▸ minpoly.natDegree_pos hx`. Distinguish the cases in `hd1 : d = 1`. Take `⟨k, hk⟩` from `(minpoly.natDegree_eq_one_iff).1 (hxd.trans hd1)`. Use `⟨(k : PadicAlgCl p), k.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hk]`. Express the relevant statement in the definitionally equal form `‖(k : PadicAlgCl p) - (k : PadicAlgCl p)‖ ≤ _`. Rewrite using `[sub_self, norm_zero]`. Conclude with `mul_nonneg (Real.rpow_nonneg (by linarith) _) hρ0`. Establish `hd2 : 2 ≤ d` using `by omega`.

Use `set k := Nat.log p d with hk`. Establish `hk1 : p ^ k ≤ d` using `Nat.pow_log_le_self p (by omega)`. Establish `hk2 : d < p ^ (k + 1)` using `Nat.lt_pow_succ_log_self hp.out.one_lt d`. Establish `hpk : 0 < p ^ k` using `pow_pos hp.out.pos k`. Distinguish the cases in `hpow : d = p ^ k`.

Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, k = j + 1 := by`. Use `⟨k - 1, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos k with h0 | h0` into its components or cases. Rewrite `hpow` using `[h0, pow_zero]`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Establish `hqd : p ^ j < d`. Rewrite using `[hpow, hj, pow_succ]`. Conclude with `lt_mul_of_one_lt_right (pow_pos hp.out.pos j) hp.out.one_lt`. Take `⟨b, hbdeg, hb⟩` from `exists_close_of_hasseDeriv x hρ (hxd ▸ hqd)`.

Rewrite `hbdeg`, `hb` using `[hxd]`. Use `set m := d - p ^ j with hm`. Establish `hm0 : m ≠ 0` using `by omega`. Establish `hmreal : (m : ℝ) = (p : ℝ) ^ j * ((p : ℝ) - 1)`. Rewrite using `[hm, Nat.cast_sub hqd.le, hpow, hj]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hmpos : (0 : ℝ) < m` using `by positivity`. Establish `hchoose : (p : ℝ)⁻¹ ≤ ‖((Nat.choose d (p ^ j) : ℕ) : PadicAlgCl p)‖`. Establish `h` using `not_sq_dvd_choose_pow_pow (p := p) (k := k) (by omega)`.

Rewrite `h` using `[hj, Nat.add_sub_cancel]`. Rewrite using `[hpow, hj]`. Conclude with `inv_le_norm_natCast_padicAlgCl (Nat.choose_pos (by`. Rewrite using `[pow_succ]`. Conclude with `Nat.le_mul_of_pos_right _ hp.out.pos)).ne' h`.

Use `set c : ℝ := (p : ℝ) ^ ((1 : ℝ) / m) with hc`. Establish `hc1 : 1 ≤ c` using `Real.one_le_rpow hp1.le (by positivity)`. Establish `hcm : c ^ m = p`. Rewrite using `[hc, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div, inv_mul_cancel₀ hmpos.ne', Real.rpow_one]`. Establish `hxb : ‖x - b‖ ≤ c * ρ`.

Assume the negation of the conclusion as `hlt`. Use `replace hlt := lt_of_not_ge hlt`. Establish `h1 : (c * ρ) ^ m < ‖x - b‖ ^ m` using `pow_lt_pow_left₀ hlt (mul_nonneg (by linarith) hρ0) hm0`. Rewrite `h1` using `[mul_pow, hcm]`. Establish `h2 : (p : ℝ)⁻¹ * ‖x - b‖ ^ m ≤ ρ ^ m` using `(mul_le_mul_of_nonneg_right hchoose (pow_nonneg (norm_nonneg _) _)).trans hb`.

Establish `h3 : ‖x - b‖ ^ m ≤ p * ρ ^ m`. Rewrite `h2` using `[inv_mul_le_iff₀ (by linarith)]`. Conclude with `h2`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hρc : ρ ≤ c * ρ` using `le_mul_of_one_le_left hρ0 hc1`.

Establish `hbρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ b - b‖ ≤ c * ρ` using `fun σ => (norm_gal_apply_sub_le x b hρ σ).trans (max_le hxb hρc)`. Establish `hpj : 0 < p ^ j` using `pow_pos hp.out.pos j`. Establish `hbd : (minpoly K b).natDegree < d` using `by omega`. Take `⟨y, hyK, hy⟩` from `IH _ hbd b rfl (c * ρ) hbρ`. Use `⟨y, hyK, ?_⟩` and prove the remaining obligations.

Establish `hlog : Nat.log p (minpoly K b).natDegree ≤ j`. Establish `hb0 : (minpoly K b).natDegree ≠ 0` using `(minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral b)).ne'`. Establish `: (minpoly K b).natDegree < p ^ (j + 1)`. Rewrite using `[← hj]`. Use linear arithmetic over natural numbers and integers.

Conclude with `Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hb0 this)`. Establish `hEk : (p : ℝ) ^ axExponent p k = (p : ℝ) ^ axExponent p j * c`. Rewrite using `[hj, axExponent_succ, Real.rpow_add (by linarith), hc, hmreal]`. Establish `hy' : ‖b - y‖ ≤ (p : ℝ) ^ axExponent p j * (c * ρ)` using `hy.trans (mul_le_mul_of_nonneg_right (rpow_axExponent_mono hlog) (mul_nonneg (by linarith) hρ0))`. Use `(norm_sub_le_max_of_le hxb hy').trans (max_le ?_ ?_)` and prove the remaining obligations.

Rewrite using `[hEk, mul_assoc]`. Conclude with `le_mul_of_one_le_left (mul_nonneg (by linarith) hρ0) (one_le_rpow_axExponent j)`. Rewrite using `[hEk, mul_assoc]`. Establish `hlt : p ^ k < d` using `lt_of_le_of_ne hk1 (Ne.symm hpow)`. Establish `hqd : d - p ^ k < d` using `by omega`.

Take `⟨b, hbdeg, hb⟩` from `exists_close_of_hasseDeriv x hρ (hxd ▸ hqd)`. Rewrite `hbdeg`, `hb` using `[hxd]`. Establish `hm : d - (d - p ^ k) = p ^ k` using `by omega`. Rewrite `hb` using `[hm, Nat.choose_symm hk1, norm_natCast_padicAlgCl_of_not_dvd (not_dvd_choose_pow_of_lt hk1 hk2), one_mul]`. Rewrite `hbdeg` using `[hm]`.

Establish `hxb : ‖x - b‖ ≤ ρ` using `(pow_le_pow_iff_left₀ (norm_nonneg _) hρ0 hpk.ne').1 hb`. Establish `hbρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ b - b‖ ≤ ρ` using `fun σ => (norm_gal_apply_sub_le x b hρ σ).trans (max_le hxb le_rfl)`. Establish `hbd : (minpoly K b).natDegree < d` using `by omega`. Take `⟨y, hyK, hy⟩` from `IH _ hbd b rfl ρ hbρ`. Use `⟨y, hyK, ?_⟩` and prove the remaining obligations.

Establish `hy' : ‖b - y‖ ≤ (p : ℝ) ^ axExponent p k * ρ` using `hy.trans (mul_le_mul_of_nonneg_right (rpow_axExponent_mono (Nat.log_mono_right hbd.le)) hρ0)`. Use `(norm_sub_le_max_of_le hxb hy').trans (max_le ?_ le_rfl)` and prove the remaining obligations. Conclude with `le_mul_of_one_le_left hρ0 (one_le_rpow_axExponent k)`.
-/
theorem ax_lemma_of_natDegree (d : ℕ) : ∀ x : PadicAlgCl p, (minpoly K x).natDegree = d →
    ∀ ρ : ℝ, (∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ ρ) →
      ∃ y ∈ K, ‖x - y‖ ≤ (p : ℝ) ^ axExponent p (Nat.log p d) * ρ := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
  intro x hxd ρ hρ
  have hx : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hρ0 : 0 ≤ ρ := by simpa using hρ 1
  have hp1 := one_lt_prime_cast (p := p)
  have hdpos : 0 < d := hxd ▸ minpoly.natDegree_pos hx

  by_cases hd1 : d = 1
  · obtain ⟨k, hk⟩ := (minpoly.natDegree_eq_one_iff).1 (hxd.trans hd1)
    refine ⟨(k : PadicAlgCl p), k.2, ?_⟩
    rw [← hk]
    change ‖(k : PadicAlgCl p) - (k : PadicAlgCl p)‖ ≤ _
    rw [sub_self, norm_zero]
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) hρ0
  have hd2 : 2 ≤ d := by omega
  set k := Nat.log p d with hk
  have hk1 : p ^ k ≤ d := Nat.pow_log_le_self p (by omega)
  have hk2 : d < p ^ (k + 1) := Nat.lt_pow_succ_log_self hp.out.one_lt d
  have hpk : 0 < p ^ k := pow_pos hp.out.pos k
  by_cases hpow : d = p ^ k
  ·
    obtain ⟨j, hj⟩ : ∃ j, k = j + 1 := by
      refine ⟨k - 1, ?_⟩
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, pow_zero] at hpow; omega
      · omega
    have hqd : p ^ j < d := by
      rw [hpow, hj, pow_succ]
      exact lt_mul_of_one_lt_right (pow_pos hp.out.pos j) hp.out.one_lt
    obtain ⟨b, hbdeg, hb⟩ := exists_close_of_hasseDeriv x hρ (hxd ▸ hqd)
    rw [hxd] at hbdeg hb
    set m := d - p ^ j with hm
    have hm0 : m ≠ 0 := by omega
    have hmreal : (m : ℝ) = (p : ℝ) ^ j * ((p : ℝ) - 1) := by
      rw [hm, Nat.cast_sub hqd.le, hpow, hj]
      push_cast
      ring
    have hmpos : (0 : ℝ) < m := by positivity

    have hchoose : (p : ℝ)⁻¹ ≤ ‖((Nat.choose d (p ^ j) : ℕ) : PadicAlgCl p)‖ := by
      have h := not_sq_dvd_choose_pow_pow (p := p) (k := k) (by omega)
      rw [hj, Nat.add_sub_cancel] at h
      rw [hpow, hj]
      exact inv_le_norm_natCast_padicAlgCl (Nat.choose_pos (by
        rw [pow_succ]; exact Nat.le_mul_of_pos_right _ hp.out.pos)).ne' h
    set c : ℝ := (p : ℝ) ^ ((1 : ℝ) / m) with hc
    have hc1 : 1 ≤ c := Real.one_le_rpow hp1.le (by positivity)
    have hcm : c ^ m = p := by
      rw [hc, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div,
        inv_mul_cancel₀ hmpos.ne', Real.rpow_one]
    have hxb : ‖x - b‖ ≤ c * ρ := by
      by_contra hlt
      replace hlt := lt_of_not_ge hlt
      have h1 : (c * ρ) ^ m < ‖x - b‖ ^ m :=
        pow_lt_pow_left₀ hlt (mul_nonneg (by linarith) hρ0) hm0
      rw [mul_pow, hcm] at h1
      have h2 : (p : ℝ)⁻¹ * ‖x - b‖ ^ m ≤ ρ ^ m :=
        (mul_le_mul_of_nonneg_right hchoose (pow_nonneg (norm_nonneg _) _)).trans hb
      have h3 : ‖x - b‖ ^ m ≤ p * ρ ^ m := by
        rw [inv_mul_le_iff₀ (by linarith)] at h2
        exact h2
      linarith
    have hρc : ρ ≤ c * ρ := le_mul_of_one_le_left hρ0 hc1
    have hbρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ b - b‖ ≤ c * ρ := fun σ =>
      (norm_gal_apply_sub_le x b hρ σ).trans (max_le hxb hρc)
    have hpj : 0 < p ^ j := pow_pos hp.out.pos j
    have hbd : (minpoly K b).natDegree < d := by omega
    obtain ⟨y, hyK, hy⟩ := IH _ hbd b rfl (c * ρ) hbρ
    refine ⟨y, hyK, ?_⟩
    have hlog : Nat.log p (minpoly K b).natDegree ≤ j := by
      have hb0 : (minpoly K b).natDegree ≠ 0 :=
        (minpoly.natDegree_pos (Algebra.IsIntegral.isIntegral b)).ne'
      have : (minpoly K b).natDegree < p ^ (j + 1) := by
        rw [← hj]; omega
      exact Nat.lt_succ_iff.1 (Nat.log_lt_of_lt_pow hb0 this)
    have hEk : (p : ℝ) ^ axExponent p k = (p : ℝ) ^ axExponent p j * c := by
      rw [hj, axExponent_succ, Real.rpow_add (by linarith), hc, hmreal]
    have hy' : ‖b - y‖ ≤ (p : ℝ) ^ axExponent p j * (c * ρ) :=
      hy.trans (mul_le_mul_of_nonneg_right (rpow_axExponent_mono hlog)
        (mul_nonneg (by linarith) hρ0))
    refine (norm_sub_le_max_of_le hxb hy').trans (max_le ?_ ?_)
    · rw [hEk, mul_assoc]
      exact le_mul_of_one_le_left (mul_nonneg (by linarith) hρ0) (one_le_rpow_axExponent j)
    · rw [hEk, mul_assoc]
  ·
    have hlt : p ^ k < d := lt_of_le_of_ne hk1 (Ne.symm hpow)
    have hqd : d - p ^ k < d := by omega
    obtain ⟨b, hbdeg, hb⟩ := exists_close_of_hasseDeriv x hρ (hxd ▸ hqd)
    rw [hxd] at hbdeg hb
    have hm : d - (d - p ^ k) = p ^ k := by omega
    rw [hm, Nat.choose_symm hk1,
      norm_natCast_padicAlgCl_of_not_dvd (not_dvd_choose_pow_of_lt hk1 hk2), one_mul] at hb
    rw [hm] at hbdeg
    have hxb : ‖x - b‖ ≤ ρ := (pow_le_pow_iff_left₀ (norm_nonneg _) hρ0 hpk.ne').1 hb
    have hbρ : ∀ σ : Gal(PadicAlgCl p/K), ‖σ b - b‖ ≤ ρ := fun σ =>
      (norm_gal_apply_sub_le x b hρ σ).trans (max_le hxb le_rfl)
    have hbd : (minpoly K b).natDegree < d := by omega
    obtain ⟨y, hyK, hy⟩ := IH _ hbd b rfl ρ hbρ
    refine ⟨y, hyK, ?_⟩
    have hy' : ‖b - y‖ ≤ (p : ℝ) ^ axExponent p k * ρ :=
      hy.trans (mul_le_mul_of_nonneg_right (rpow_axExponent_mono
        (Nat.log_mono_right hbd.le)) hρ0)
    refine (norm_sub_le_max_of_le hxb hy').trans (max_le ?_ le_rfl)
    exact le_mul_of_one_le_left hρ0 (one_le_rpow_axExponent k)

end Induction

section Ax

variable {p : ℕ} [hp : Fact p.Prime]

def axConstant (p : ℕ) : ℝ := (p : ℝ) ^ ((p : ℝ) / ((p : ℝ) - 1) ^ 2)

/- English proof (translation)
The claim follows from `Real.one_le_rpow one_lt_prime_cast.le (div_nonneg (by linarith [one_lt_prime_cast (p := p)]) (sq_nonneg _))`.
-/
theorem one_le_axConstant : 1 ≤ axConstant p :=
  Real.one_le_rpow one_lt_prime_cast.le (div_nonneg (by linarith [one_lt_prime_cast (p := p)])
    (sq_nonneg _))

/- English proof (translation)
The claim follows from `one_le_axConstant.trans_lt' one_pos`.
-/
theorem axConstant_pos : 0 < axConstant p := one_le_axConstant.trans_lt' one_pos

/- English proof (translation)
Take `⟨y, hy, hle⟩` from `ax_lemma_of_natDegree _ x rfl r h`. Establish `hr : 0 ≤ r` using `by simpa using h 1`. Conclude with `⟨y, hy, hle.trans (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le one_lt_prime_cast.le (axExponent_le _)) hr)⟩`.
-/
theorem ax_lemma {K : IntermediateField ℚ_[p] (PadicAlgCl p)} (x : PadicAlgCl p) {r : ℝ}
    (h : ∀ σ : Gal(PadicAlgCl p/K), ‖σ x - x‖ ≤ r) :
    ∃ y ∈ K, ‖x - y‖ ≤ axConstant p * r := by
  obtain ⟨y, hy, hle⟩ := ax_lemma_of_natDegree _ x rfl r h
  have hr : 0 ≤ r := by simpa using h 1
  exact ⟨y, hy, hle.trans (mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_of_exponent_le one_lt_prime_cast.le (axExponent_le _)) hr)⟩

end Ax

section AxSenTate

open UniformSpace Topology

variable {p : ℕ} [hp : Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

/- English proof (translation)
Establish `: {x : ℂ_[p] | ∀ σ ∈ S, σ • x = x} = ⋂ σ ∈ S, {x : ℂ_[p] | σ • x = x}`. Use extensionality with `x`. Simplify using the standard rewrite rules. Rewrite using `[this]`. Conclude with `isClosed_biInter fun σ _ => isClosed_eq (continuous_const_smul σ) continuous_id`.
-/
theorem isClosed_setOf_forall_smul_eq (S : Set Gal(PadicAlgCl p/K)) :
    IsClosed {x : ℂ_[p] | ∀ σ ∈ S, σ • x = x} := by
  have : {x : ℂ_[p] | ∀ σ ∈ S, σ • x = x} = ⋂ σ ∈ S, {x : ℂ_[p] | σ • x = x} := by
    ext x; simp
  rw [this]
  exact isClosed_biInter fun σ _ => isClosed_eq (continuous_const_smul σ) continuous_id

/- English proof (translation)
Use `subset_antisymm ?_ (closure_minimal ?_ (isClosed_setOf_forall_smul_eq S))` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[Metric.mem_closure_iff]`. Introduce `ε hε`. Use `set δ := ε / (C + 1) with hδ`.

Establish `hδ0 : 0 < δ` using `div_pos hε (by linarith)`. Establish `hδε : δ < ε` using `div_lt_self hε (by linarith)`. Establish `hCδ : C * δ < ε`. Rewrite using `[hδ, mul_div_assoc', div_lt_iff₀ (by linarith)]`. Use the polynomial consequences of the given equalities and inequalities.

Take `⟨_, ⟨z, rfl⟩, hxz⟩` from `Metric.mem_closure_iff.1 (Completion.denseRange_coe (α := PadicAlgCl p) x) δ hδ0`. Rewrite `hxz` using `[dist_eq_norm]`. Establish `hmove : ∀ σ ∈ S, ‖σ z - z‖ ≤ δ`. Introduce `σ hσ`. Rewrite using `[← PadicComplex.norm_extends, Completion.coe_sub, ← gal_smul_coe]`.

Establish `h1 : σ • (z : ℂ_[p]) - (z : ℂ_[p]) = σ • ((z : ℂ_[p]) - x) - ((z : ℂ_[p]) - x)`. Rewrite using `[smul_sub, hx σ hσ]`. Normalize the expressions using the abelian group laws. Rewrite using `[h1, sub_eq_add_neg]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations.

Rewrite using `[norm_smul_gal, norm_sub_rev]`. Conclude with `hxz.le`. Rewrite using `[norm_neg, norm_sub_rev]`. Conclude with `hxz.le`. Take `⟨y, hyL, hy⟩` from `hax z δ hmove`.

Use `⟨(y : ℂ_[p]), ⟨y, hyL, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dist_eq_norm, ← sub_add_sub_cancel x (z : ℂ_[p]) (y : ℂ_[p])]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hxz.trans hδε) ?_)` and prove the remaining obligations. Rewrite using `[← Completion.coe_sub, PadicComplex.norm_extends]`. Conclude with `hy.trans_lt hCδ`.

Introduce and unpack `_ ⟨y, hy, rfl⟩ σ hσ`. Rewrite using `[gal_smul_coe, hL y hy σ hσ]`.
-/
theorem setOf_forall_smul_eq_eq_closure (S : Set Gal(PadicAlgCl p/K)) (L : Set (PadicAlgCl p))
    (hL : ∀ y ∈ L, ∀ σ ∈ S, σ y = y) {C : ℝ} (hC : 0 < C)
    (hax : ∀ z : PadicAlgCl p, ∀ r : ℝ, (∀ σ ∈ S, ‖σ z - z‖ ≤ r) → ∃ y ∈ L, ‖z - y‖ ≤ C * r) :
    {x : ℂ_[p] | ∀ σ ∈ S, σ • x = x} = closure (((↑) : PadicAlgCl p → ℂ_[p]) '' L) := by
  refine subset_antisymm ?_ (closure_minimal ?_ (isClosed_setOf_forall_smul_eq S))
  · intro x hx
    rw [Metric.mem_closure_iff]
    intro ε hε
    set δ := ε / (C + 1) with hδ
    have hδ0 : 0 < δ := div_pos hε (by linarith)
    have hδε : δ < ε := div_lt_self hε (by linarith)
    have hCδ : C * δ < ε := by
      rw [hδ, mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    obtain ⟨_, ⟨z, rfl⟩, hxz⟩ := Metric.mem_closure_iff.1
      (Completion.denseRange_coe (α := PadicAlgCl p) x) δ hδ0
    rw [dist_eq_norm] at hxz
    have hmove : ∀ σ ∈ S, ‖σ z - z‖ ≤ δ := by
      intro σ hσ
      rw [← PadicComplex.norm_extends, Completion.coe_sub, ← gal_smul_coe]
      have h1 : σ • (z : ℂ_[p]) - (z : ℂ_[p]) = σ • ((z : ℂ_[p]) - x) - ((z : ℂ_[p]) - x) := by
        rw [smul_sub, hx σ hσ]; abel
      rw [h1, sub_eq_add_neg]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_smul_gal, norm_sub_rev]; exact hxz.le
      · rw [norm_neg, norm_sub_rev]; exact hxz.le
    obtain ⟨y, hyL, hy⟩ := hax z δ hmove
    refine ⟨(y : ℂ_[p]), ⟨y, hyL, rfl⟩, ?_⟩
    rw [dist_eq_norm, ← sub_add_sub_cancel x (z : ℂ_[p]) (y : ℂ_[p])]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (hxz.trans hδε) ?_)
    rw [← Completion.coe_sub, PadicComplex.norm_extends]
    exact hy.trans_lt hCδ
  · rintro _ ⟨y, hy, rfl⟩ σ hσ
    rw [gal_smul_coe, hL y hy σ hσ]

/- English proof (translation)
Establish `h` using `setOf_forall_smul_eq_eq_closure (K := K) Set.univ (K : Set (PadicAlgCl p)) (fun y hy σ _ => σ.commutes ⟨y, hy⟩) axConstant_pos (fun z r hz => ax_lemma z fun σ => hz σ (Set.mem_univ σ))`. Rewrite using `[← h]`. Use extensionality with `x`. Simplify using `[MulAction.mem_fixedPoints]`.
-/
theorem fixedPoints_gal_eq_closure :
    MulAction.fixedPoints Gal(PadicAlgCl p/K) ℂ_[p] =
      closure (((↑) : PadicAlgCl p → ℂ_[p]) '' (K : Set (PadicAlgCl p))) := by
  have h := setOf_forall_smul_eq_eq_closure (K := K) Set.univ (K : Set (PadicAlgCl p))
    (fun y hy σ _ => σ.commutes ⟨y, hy⟩) axConstant_pos
    (fun z r hz => ax_lemma z fun σ => hz σ (Set.mem_univ σ))
  rw [← h]
  ext x
  simp [MulAction.mem_fixedPoints]

/- English proof (translation)
Establish `: FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule K.toSubalgebra)` using `‹FiniteDimensional ℚ_[p] K›`. Establish `hK : IsComplete (K : Set (PadicAlgCl p))` using `(Subalgebra.toSubmodule K.toSubalgebra).complete_of_finiteDimensional`. Conclude with `((isComplete_image_iff (Completion.isUniformInducing_coe (PadicAlgCl p))).2 hK).isClosed`.
-/
theorem isClosed_image_coe_of_finiteDimensional [FiniteDimensional ℚ_[p] K] :
    IsClosed (((↑) : PadicAlgCl p → ℂ_[p]) '' (K : Set (PadicAlgCl p))) := by
  have : FiniteDimensional ℚ_[p] (Subalgebra.toSubmodule K.toSubalgebra) :=
    ‹FiniteDimensional ℚ_[p] K›
  have hK : IsComplete (K : Set (PadicAlgCl p)) :=
    (Subalgebra.toSubmodule K.toSubalgebra).complete_of_finiteDimensional
  exact ((isComplete_image_iff (Completion.isUniformInducing_coe (PadicAlgCl p))).2 hK).isClosed

/- English proof (translation)
Rewrite using `[fixedPoints_gal_eq_closure, isClosed_image_coe_of_finiteDimensional.closure_eq]`.
-/
theorem fixedPoints_gal_eq [FiniteDimensional ℚ_[p] K] :
    MulAction.fixedPoints Gal(PadicAlgCl p/K) ℂ_[p] =
      ((↑) : PadicAlgCl p → ℂ_[p]) '' (K : Set (PadicAlgCl p)) := by
  rw [fixedPoints_gal_eq_closure, isClosed_image_coe_of_finiteDimensional.closure_eq]

/- English proof (translation)
Establish `: x ∈ MulAction.fixedPoints Gal(PadicAlgCl p/K) ℂ_[p]` using `hx`. Rewrite `this` using `[fixedPoints_gal_eq]`. Take `⟨y, hy, rfl⟩` from `this`. Conclude with `⟨⟨y, hy⟩, rfl⟩`.
-/
theorem exists_eq_coe_of_forall_smul_eq [FiniteDimensional ℚ_[p] K] {x : ℂ_[p]}
    (hx : ∀ σ : Gal(PadicAlgCl p/K), σ • x = x) :
    ∃ k : K, ((k : PadicAlgCl p) : ℂ_[p]) = x := by
  have : x ∈ MulAction.fixedPoints Gal(PadicAlgCl p/K) ℂ_[p] := hx
  rw [fixedPoints_gal_eq] at this
  obtain ⟨y, hy, rfl⟩ := this
  exact ⟨⟨y, hy⟩, rfl⟩

/- English proof (translation)
Use `set L := (IntermediateField.fixedField H).restrictScalars ℚ_[p] with hL`. Establish `hfix : (IntermediateField.fixedField H).fixingSubgroup = H` using `InfiniteGalois.fixingSubgroup_fixedField ⟨H, hH⟩`. Establish `hτ : ∀ τ : Gal(PadicAlgCl p/L), ‖τ z - z‖ ≤ r`. Introduce `τ`. Set `σ : Gal(PadicAlgCl p/K)` to `{ τ.toRingEquiv with commutes' := fun k => τ.commutes ⟨algebraMap K (PadicAlgCl p) k, (IntermediateField.mem_restrictScalars _).2 (IntermediateField.algebraMap_mem _ k)⟩ }`.

Establish `hσ : σ ∈ H`. Rewrite using `[← hfix, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `m hm`. Conclude with `τ.commutes ⟨m, (IntermediateField.mem_restrictScalars _).2 hm⟩`. Conclude with `hz σ hσ`.

Take `⟨y, hy, hle⟩` from `ax_lemma z hτ`. Conclude with `⟨y, (IntermediateField.mem_restrictScalars _).1 hy, hle⟩`.
-/
theorem ax_lemma_closedSubgroup (H : Subgroup Gal(PadicAlgCl p/K))
    (hH : IsClosed (H : Set Gal(PadicAlgCl p/K))) (z : PadicAlgCl p) {r : ℝ}
    (hz : ∀ σ ∈ H, ‖σ z - z‖ ≤ r) :
    ∃ y ∈ IntermediateField.fixedField H, ‖z - y‖ ≤ axConstant p * r := by
  set L := (IntermediateField.fixedField H).restrictScalars ℚ_[p] with hL
  have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨H, hH⟩
  have hτ : ∀ τ : Gal(PadicAlgCl p/L), ‖τ z - z‖ ≤ r := by
    intro τ
    let σ : Gal(PadicAlgCl p/K) :=
      { τ.toRingEquiv with
        commutes' := fun k => τ.commutes ⟨algebraMap K (PadicAlgCl p) k,
          (IntermediateField.mem_restrictScalars _).2
            (IntermediateField.algebraMap_mem _ k)⟩ }
    have hσ : σ ∈ H := by
      rw [← hfix, IntermediateField.mem_fixingSubgroup_iff]
      intro m hm
      exact τ.commutes ⟨m, (IntermediateField.mem_restrictScalars _).2 hm⟩
    exact hz σ hσ
  obtain ⟨y, hy, hle⟩ := ax_lemma z hτ
  exact ⟨y, (IntermediateField.mem_restrictScalars _).1 hy, hle⟩

/- English proof (translation)
The claim follows from `setOf_forall_smul_eq_eq_closure (H : Set Gal(PadicAlgCl p/K)) _ (fun y hy σ hσ => (IntermediateField.mem_fixedField_iff H y).1 hy σ hσ) axConstant_pos (fun z _ hz => ax_lemma_closedSubgroup H hH z hz)`.
-/
theorem fixedPoints_closedSubgroup_eq_closure (H : Subgroup Gal(PadicAlgCl p/K))
    (hH : IsClosed (H : Set Gal(PadicAlgCl p/K))) :
    {x : ℂ_[p] | ∀ σ ∈ H, σ • x = x} =
      closure (((↑) : PadicAlgCl p → ℂ_[p]) ''
        (IntermediateField.fixedField H : Set (PadicAlgCl p))) :=
  setOf_forall_smul_eq_eq_closure (H : Set Gal(PadicAlgCl p/K)) _
    (fun y hy σ hσ => (IntermediateField.mem_fixedField_iff H y).1 hy σ hσ) axConstant_pos
    (fun z _ hz => ax_lemma_closedSubgroup H hH z hz)

end AxSenTate

end

end GroundTheory.PAdicHodge
