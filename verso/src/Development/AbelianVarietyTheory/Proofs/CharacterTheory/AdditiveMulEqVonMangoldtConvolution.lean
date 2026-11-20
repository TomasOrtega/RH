import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonicFactorizationConvolutionFiniteCommAssocAddStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOneStatement

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.LogDeriv

variable {F : Type} [Field F]

/- English proof (translation)
Unfold `conv`. Use `finsum_mem_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[ha _ hx.1, hb _ hx.2.1]`.
-/
theorem conv_congr_monic {a a' b b' : F[X] → ℂ} (ha : ∀ P : F[X], P.Monic → a P = a' P)
    (hb : ∀ P : F[X], P.Monic → b P = b' P) (P : F[X]) : conv a b P = conv a' b' P := by
  unfold conv
  refine finsum_mem_congr rfl fun x hx => ?_
  rw [ha _ hx.1, hb _ hx.2.1]

/- English proof (translation)
Unfold `conv`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum]`.
-/
theorem conv_eq_sum (a b : F[X] → ℂ) {P : F[X]} (hP : P.Monic) :
    conv a b P = ∑ x ∈ (GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F P hP).1.toFinset, a x.1 * b x.2 := by
  unfold conv
  rw [finsum_mem_eq_finite_toFinset_sum]

/- English proof (translation)
Rewrite using `[conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[Set.Finite.mem_toFinset]`. Take `⟨h1, h2, h3⟩` from `hx`. Rewrite using `[← h3, h1.natDegree_mul h2, pow_add]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem pow_mul_conv (q : ℂ) (a b : F[X] → ℂ) {P : F[X]} (hP : P.Monic) :
    q ^ P.natDegree * conv a b P =
      conv (fun D => q ^ D.natDegree * a D) (fun D => q ^ D.natDegree * b D) P := by
  rw [conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  rw [← h3, h1.natDegree_mul h2, pow_add]
  ring

/- English proof (translation)
Rewrite using `[conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[Set.Finite.mem_toFinset]`. Take `⟨h1, h2, h3⟩` from `hx`. Rewrite using `[← h3, hs _ _ h1 h2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem additive_mul_conv {s : F[X] → ℂ} (hs : IsAdditive s) (a b : F[X] → ℂ) {P : F[X]}
    (hP : P.Monic) :
    s P * conv a b P = conv (fun D => s D * a D) b P + conv a (fun D => s D * b D) P := by
  rw [conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, conv_eq_sum _ _ hP, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨h1, h2, h3⟩ := hx
  rw [← h3, hs _ _ h1 h2]
  ring

/- English proof (translation)
Rewrite using `[sub_ne_zero]`. Establish `: q ^ n ≠ 1` using `(Nat.one_lt_pow hn (by omega)).ne'`. Conclude with `this` after adjusting the coercions.
-/
theorem pow_natDegree_ne_one {q : ℕ} (hq : 2 ≤ q) {n : ℕ} (hn : n ≠ 0) : (q : ℂ) ^ n - 1 ≠ 0 := by
  rw [sub_ne_zero]
  have : q ^ n ≠ 1 := (Nat.one_lt_pow hn (by omega)).ne'
  exact_mod_cast this

/- English proof (translation)
Introduce `P`. Proceed by induction on `h : P.natDegree using Nat.strong_induction_on generalizing P with`. Consider the case `_ n ih`. Introduce `hP`. Distinguish the cases in `hn : n = 0`.

Rewrite using `[hP.natDegree_eq_zero.mp (h.trans hn)]`. Conclude with `h1`. Establish `key : conv (fun _ => 1) E P = E P`. Rewrite using `[conv_eq_sum _ _ hP, Finset.sum_eq_single ((1 : F[X]), P)]`. Simplify using the standard rewrite rules.

Introduce `x hx hne`. Rewrite `hx` using `[Set.Finite.mem_toFinset]`. Take `⟨h1, h2, h3⟩` from `hx`. Establish `hd : x.1.natDegree ≠ 0`. Introduce `h0`.

Use `h1.natDegree_eq_zero.mp h0` as an intermediate fact. Apply `hne` to reduce the goal to its premises. Rewrite `h3` using `[this, one_mul]`. Conclude with `Prod.ext this h3`. Establish `hdeg` using `h1.natDegree_mul h2`.

Rewrite `hdeg` using `[h3, h]`. Rewrite using `[ih x.2.natDegree (by omega) x.2 rfl h2, mul_zero]`. Introduce `hx`. Conclude with `absurd (by simp [hP]) hx`. Establish `h2` using `hE P hP`.

Rewrite `h2` using `[key, h]`. Establish `h3 : ((q : ℂ) ^ n - 1) * E P = 0` using `by linear_combination h2`. Conclude with `(mul_eq_zero.mp h3).resolve_left (pow_natDegree_ne_one hq hn)`.
-/
theorem eq_zero_of_rec {q : ℕ} (hq : 2 ≤ q) {E : F[X] → ℂ} (h1 : E 1 = 0)
    (hE : ∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * E P = conv (fun _ => 1) E P) :
    ∀ P : F[X], P.Monic → E P = 0 := by
  intro P
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ n ih =>
    intro hP
    by_cases hn : n = 0
    · rw [hP.natDegree_eq_zero.mp (h.trans hn)]; exact h1
    have key : conv (fun _ => 1) E P = E P := by
      rw [conv_eq_sum _ _ hP, Finset.sum_eq_single ((1 : F[X]), P)]
      · simp
      · intro x hx hne
        rw [Set.Finite.mem_toFinset] at hx
        obtain ⟨h1, h2, h3⟩ := hx
        have hd : x.1.natDegree ≠ 0 := by
          intro h0
          have := h1.natDegree_eq_zero.mp h0
          apply hne
          rw [this, one_mul] at h3
          exact Prod.ext this h3
        have hdeg := h1.natDegree_mul h2
        rw [h3, h] at hdeg
        rw [ih x.2.natDegree (by omega) x.2 rfl h2, mul_zero]
      · intro hx
        exact absurd (by simp [hP]) hx
    have h2 := hE P hP
    rw [key, h] at h2
    have h3 : ((q : ℂ) ^ n - 1) * E P = 0 := by linear_combination h2
    exact (mul_eq_zero.mp h3).resolve_left (pow_natDegree_ne_one hq hn)

/- English proof (translation)
Unfold `mangoldt`. Use `finsum_mem_eq_zero_of_forall_eq_zero ?_` and prove the remaining obligations. Introduce and unpack `f ⟨_, hf, m, hm, h⟩`. Conclude with `absurd (IsUnit.of_pow_eq_one h.symm hm.ne') hf.not_isUnit`.
-/
theorem mangoldt_one (s : F[X] → ℂ) : mangoldt s 1 = 0 := by
  unfold mangoldt
  refine finsum_mem_eq_zero_of_forall_eq_zero ?_
  rintro f ⟨_, hf, m, hm, h⟩
  exact absurd (IsUnit.of_pow_eq_one h.symm hm.ne') hf.not_isUnit

/- English proof (translation)
Unfold `conv`. Establish `: {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = 1} = {(1, 1)}`. Use extensionality with `x`. Simplify using `only [Set.mem_setOf_eq, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2, h3⟩`. Establish `hdeg` using `h1.natDegree_mul h2`. Rewrite `hdeg` using `[h3, natDegree_one]`. Conclude with `Prod.ext (h1.natDegree_eq_zero.mp (by omega)) (h2.natDegree_eq_zero.mp (by omega))`. Introduce and unpack `rfl`.

Simplify using the standard rewrite rules. Rewrite using `[this, finsum_mem_singleton]`.
-/
theorem conv_at_one (a b : F[X] → ℂ) : conv a b 1 = a 1 * b 1 := by
  unfold conv
  have : {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = 1} = {(1, 1)} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      have hdeg := h1.natDegree_mul h2
      rw [h3, natDegree_one] at hdeg
      exact Prod.ext (h1.natDegree_eq_zero.mp (by omega)) (h2.natDegree_eq_zero.mp (by omega))
    · rintro rfl
      simp
  rw [this, finsum_mem_singleton]

/- English proof (translation)
Use `set L : F[X] → ℂ := fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1) with hL`. Use `set o : F[X] → ℂ := fun _ => 1 with ho`. Establish `hs1 : s 1 = 0`. Use `hs 1 1 monic_one monic_one` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Take the linear combination `-this`. Establish `hσL : ∀ D : F[X], D.Monic → (q : ℂ) ^ D.natDegree * L D = (L + mangoldt s) D`. Introduce `D hD`. Distinguish the cases in `h0 : D.natDegree = 0`. Rewrite using `[hD.natDegree_eq_zero.mp h0]`.

Simplify using `[hL, mangoldt_one]`. Use `pow_natDegree_ne_one hq h0` as an intermediate fact. Simplify using `only [hL, Pi.add_apply]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.

Establish `hA : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * (s Q * m Q) = conv (conv (mangoldt s) o) m Q + conv o (fun D => s D * m D) Q`. Introduce `Q hQ`. Rewrite using `[mul_left_comm, hm Q hQ, additive_mul_conv hs _ _ hQ]`. Use `congr 1`. Use `conv_congr_monic (fun D hD => ?_) (fun _ _ => rfl) Q` and prove the remaining obligations.

Rewrite using `[← (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F s hs).1 D hD]`. Simplify using `[ho]`. Establish `hB : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * conv L m Q = conv (conv (mangoldt s) o) m Q + conv o (conv L m) Q`. Introduce `Q hQ`. Establish `H` using `(GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F Q hQ).2`.

Rewrite using `[pow_mul_conv _ _ _ hQ, conv_congr_monic hσL hm Q, (H L (mangoldt s) (conv o m)).2.2.1, (H (mangoldt s) o m).2.1, add_comm, ← (H L o m).2.1, ← (H o L m).2.1]`. Use `congr 1`. Conclude with `conv_congr_monic (fun D hD => ((GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F D hD).2 L o o).1) (fun _ _ => rfl) Q`. Establish `hE` using `eq_zero_of_rec hq (E := (fun D => s D * m D) - conv L m) (by simp [hs1, conv_at_one, hL, mangoldt_one]) (fun Q hQ => by`. Establish `H` using `(GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F Q hQ).2`.

Rewrite using `[(H _ _ o).1, (H _ _ _).2.2.2, ← (H o _ o).1, ← (H o _ o).1, Pi.sub_apply, mul_sub, hA Q hQ, hB Q hQ]`. Use the proof step `ring) P hP`. Conclude with `sub_eq_zero.mp hE`.
-/
theorem additive_mul_eq_conv (F : Type) [Field F] (q : ℕ) (hq : 2 ≤ q) (s m : F[X] → ℂ)
    (hs : IsAdditive s) (_hm1 : m 1 = 1)
    (hm : ∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * m P = conv (fun _ => 1) m P)
    (P : F[X]) (hP : P.Monic) :
    s P * m P = conv (fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1)) m P := by
  set L : F[X] → ℂ := fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1) with hL
  set o : F[X] → ℂ := fun _ => 1 with ho
  have hs1 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    rw [mul_one] at this
    linear_combination -this
  have hσL : ∀ D : F[X], D.Monic → (q : ℂ) ^ D.natDegree * L D = (L + mangoldt s) D := by
    intro D hD
    by_cases h0 : D.natDegree = 0
    · rw [hD.natDegree_eq_zero.mp h0]
      simp [hL, mangoldt_one]
    · have := pow_natDegree_ne_one hq h0
      simp only [hL, Pi.add_apply]
      field_simp
      ring
  have hA : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * (s Q * m Q) =
      conv (conv (mangoldt s) o) m Q + conv o (fun D => s D * m D) Q := by
    intro Q hQ
    rw [mul_left_comm, hm Q hQ, additive_mul_conv hs _ _ hQ]
    congr 1
    refine conv_congr_monic (fun D hD => ?_) (fun _ _ => rfl) Q
    rw [← (GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one F s hs).1 D hD]
    simp [ho]
  have hB : ∀ Q : F[X], Q.Monic → (q : ℂ) ^ Q.natDegree * conv L m Q =
      conv (conv (mangoldt s) o) m Q + conv o (conv L m) Q := by
    intro Q hQ
    have H := (GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F Q hQ).2
    rw [pow_mul_conv _ _ _ hQ, conv_congr_monic hσL hm Q, (H L (mangoldt s) (conv o m)).2.2.1,
      (H (mangoldt s) o m).2.1, add_comm, ← (H L o m).2.1, ← (H o L m).2.1]
    congr 1
    exact conv_congr_monic (fun D hD => ((GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F D hD).2 L o o).1) (fun _ _ => rfl) Q
  have hE := eq_zero_of_rec hq (E := (fun D => s D * m D) - conv L m)
    (by simp [hs1, conv_at_one, hL, mangoldt_one]) (fun Q hQ => by
      have H := (GlobalTheory.T.monicFactorizationConvolution_finite_comm_assoc_add F Q hQ).2
      rw [(H _ _ o).1, (H _ _ _).2.2.2, ← (H o _ o).1, ← (H o _ o).1, Pi.sub_apply, mul_sub,
        hA Q hQ, hB Q hQ]
      ring) P hP
  exact sub_eq_zero.mp hE

end GlobalTheory.CuspGL.LogDeriv
