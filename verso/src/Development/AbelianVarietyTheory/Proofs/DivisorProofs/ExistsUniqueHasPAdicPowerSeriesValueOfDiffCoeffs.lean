import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.ValEx

/- English proof (translation)
Use `set T := 2 * N + m + 1 with hT`. Establish `hT2 : T < 2 ^ T` using `Nat.lt_two_pow_self`. Establish `hA : ∀ v, 2 * T ≤ v → N * (m + v) ≤ 2 ^ v`. Introduce `v hv`. Proceed by induction on `v, hv using Nat.le_induction with`.

Consider the case `base`. Establish `hNT : N ≤ T` using `by omega`. Establish `h1 : N * (m + 2 * T) ≤ T * T` using `by nlinarith [Nat.mul_le_mul_right m hNT]`. Establish `h2 : T * T ≤ 2 ^ T * 2 ^ T` using `Nat.mul_le_mul hT2.le hT2.le`. Combine the equalities or inequalities in the displayed calculation.

Consider the case `succ v hv ih`. Establish `h3 : N ≤ 2 ^ v`. Establish `: 2 ^ T ≤ 2 ^ v` using `Nat.pow_le_pow_right (by norm_num) (by omega)`. Use linear arithmetic over natural numbers and integers. Rewrite using `[pow_succ]`.

Use the polynomial consequences of the given equalities and inequalities. Use `⟨N * (m + 2 * T) + 1, by omega, fun a v ha hv => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hvK : 2 * T ≤ v`. Combine the equalities or inequalities in the displayed calculation. Establish `: N * (m + v) ≤ N * (m + 2 * T)` using `Nat.mul_le_mul_left _ (by omega)`.

Use linear arithmetic over natural numbers and integers.
-/
theorem nat_bound (p N m : ℕ) (hp : 2 ≤ p) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ a v : ℕ, M ≤ a → p ^ v ≤ a → N * (m + v) ≤ a := by
  set T := 2 * N + m + 1 with hT
  have hT2 : T < 2 ^ T := Nat.lt_two_pow_self
  have hA : ∀ v, 2 * T ≤ v → N * (m + v) ≤ 2 ^ v := by
    intro v hv
    induction v, hv using Nat.le_induction with
    | base =>
      have hNT : N ≤ T := by omega
      have h1 : N * (m + 2 * T) ≤ T * T := by nlinarith [Nat.mul_le_mul_right m hNT]
      have h2 : T * T ≤ 2 ^ T * 2 ^ T := Nat.mul_le_mul hT2.le hT2.le
      calc N * (m + 2 * T) ≤ T * T := h1
        _ ≤ 2 ^ T * 2 ^ T := h2
        _ = 2 ^ (2 * T) := by rw [← pow_add, two_mul]
    | succ v hv ih =>
      have h3 : N ≤ 2 ^ v := by
        have : 2 ^ T ≤ 2 ^ v := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      rw [pow_succ]; nlinarith
  refine ⟨N * (m + 2 * T) + 1, by omega, fun a v ha hv => ?_⟩
  by_cases hvK : 2 * T ≤ v
  · calc N * (m + v) ≤ 2 ^ v := hA v hvK
      _ ≤ p ^ v := Nat.pow_le_pow_left hp v
      _ ≤ a := hv
  · have : N * (m + v) ≤ N * (m + 2 * T) := Nat.mul_le_mul_left _ (by omega)
    omega

def img (B : Type) {Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] (p m : ℕ) : AddSubgroup Q where
  carrier := {x | ∃ b : B, x = algebraMap B Q ((p : B) ^ m * b)}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by rw [mul_add, map_add]⟩
  neg_mem' := by
    rintro _ ⟨a, rfl⟩
    exact ⟨-a, by rw [mul_neg, map_neg]⟩

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ : Type} [Fintype σ] [DecidableEq σ]

def box (σ : Type) [Fintype σ] (n : ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => n

def psum (z : σ → B) (f : MvPowerSeries σ Q) (n : ℕ) : Q :=
  MvPolynomial.eval (fun i => algebraMap B Q (z i)) (trunc' Q (box σ n) f)

/- English proof (translation)
Simplify using `only [psum, trunc', truncFinset_apply, map_sum, MvPolynomial.eval_monomial]`. Use `Finset.sum_congr rfl fun α _ => ?_` and prove the remaining obligations. Rewrite using `[map_finsuppProd]`. Simplify using `[map_pow]`.
-/
theorem psum_eq (z : σ → B) (f : MvPowerSeries σ Q) (n : ℕ) :
    psum z f n = ∑ α ∈ Finset.Iic (box σ n),
      coeff α f * algebraMap B Q (α.prod fun i e => z i ^ e) := by
  simp only [psum, trunc', truncFinset_apply, map_sum, MvPolynomial.eval_monomial]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_finsuppProd]
  simp [map_pow]

/- English proof (translation)
Simplify `h` using `[box, Finset.mem_Iic, Finsupp.le_def]`.
-/
theorem exists_lt_of_not_mem_box {n : ℕ} {α : σ →₀ ℕ} (h : α ∉ Finset.Iic (box σ n)) :
    ∃ i, n < α i := by
  simpa [box, Finset.mem_Iic, Finsupp.le_def] using h

/- English proof (translation)
The claim follows from `Finset.Iic_subset_Iic.2 (Finsupp.le_def.2 fun i => by simpa [box] using h)`.
-/
theorem box_mono {n n' : ℕ} (h : n ≤ n') : Finset.Iic (box σ n) ⊆ Finset.Iic (box σ n') :=
  Finset.Iic_subset_Iic.2 (Finsupp.le_def.2 fun i => by simpa [box] using h)

/- English proof (translation)
Use `choose Nf hNf using hz`. Use `set N := ∑ i, Nf i`. Establish `hN : ∀ i, (p : B) ∣ z i ^ N` using `fun i => (hNf i).trans (pow_dvd_pow _ (Finset.single_le_sum (fun j _ => Nat.zero_le (Nf j)) (Finset.mem_univ i)))`. Take `⟨M, hM1, hM⟩` from `nat_bound p N m hp.out.two_le`. Use `⟨M, fun α i hi => ?_⟩` and prove the remaining obligations.

Establish `ha0 : α i ≠ 0` using `by omega`. Take `⟨v, u, hu, hau⟩` from `Nat.exists_eq_pow_mul_and_not_dvd ha0 p hp.out.ne_one`. Establish `hcop : Nat.Coprime u p` using `Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu)`. Take `⟨U, hU⟩` from `hunit u hcop`. Establish `hle : N * (m + v) ≤ α i` using `hM (α i) v hi (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) ⟨u, hau⟩)`.

Establish `hdz : (p : B) ^ (m + v) ∣ z i ^ (α i)` using `(pow_dvd_pow_of_dvd (hN i) (m + v)).trans (by rw [← pow_mul]; exact pow_dvd_pow _ hle)`. Establish `hprod : z i ^ (α i) ∣ α.prod fun j e => z j ^ e`. Establish `hi' : i ∈ α.support` using `Finsupp.mem_support_iff.2 ha0`. Unfold `Finsupp.prod`. Conclude with `Finset.dvd_prod_of_mem (fun j => z j ^ α j) hi'`.

Take `⟨r, hr⟩` from `hdz.trans hprod`. Take `⟨b, -, hb⟩` from `hf α i`. Use `⟨b * ↑U⁻¹ * r, ?_⟩` and prove the remaining obligations. Rewrite using `[hr]`. Rewrite `hb` using `[hau]`.

Establish `hUU : (u : Q) * algebraMap B Q (↑U⁻¹ : B) = 1`. Rewrite using `[← map_natCast (algebraMap B Q), ← map_mul, ← hU, Units.mul_inv, map_one]`. Simplify using `only [map_mul, map_pow, map_natCast]`. Move the coercions through the operations in `at hb`. Take the linear combination `((p : Q) ^ m * algebraMap B Q (↑U⁻¹ : B) * algebraMap B Q r) * hb - (coeff α f * (p : Q) ^ (m + v) * algebraMap B Q r) * hUU`.
-/
theorem term_mem (p : ℕ) [hp : Fact p.Prime] (hunit : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B))
    (z : σ → B) (hz : ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) (m : ℕ) :
    ∃ M : ℕ, ∀ (α : σ →₀ ℕ) (i : σ), M ≤ α i →
      coeff α f * algebraMap B Q (α.prod fun i e => z i ^ e) ∈ img B p m := by
  choose Nf hNf using hz
  set N := ∑ i, Nf i
  have hN : ∀ i, (p : B) ∣ z i ^ N := fun i => (hNf i).trans
    (pow_dvd_pow _ (Finset.single_le_sum (fun j _ => Nat.zero_le (Nf j)) (Finset.mem_univ i)))
  obtain ⟨M, hM1, hM⟩ := nat_bound p N m hp.out.two_le
  refine ⟨M, fun α i hi => ?_⟩
  have ha0 : α i ≠ 0 := by omega
  obtain ⟨v, u, hu, hau⟩ := Nat.exists_eq_pow_mul_and_not_dvd ha0 p hp.out.ne_one
  have hcop : Nat.Coprime u p := Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hu)
  obtain ⟨U, hU⟩ := hunit u hcop
  have hle : N * (m + v) ≤ α i := hM (α i) v hi (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) ⟨u, hau⟩)
  have hdz : (p : B) ^ (m + v) ∣ z i ^ (α i) :=
    (pow_dvd_pow_of_dvd (hN i) (m + v)).trans (by rw [← pow_mul]; exact pow_dvd_pow _ hle)
  have hprod : z i ^ (α i) ∣ α.prod fun j e => z j ^ e := by
    have hi' : i ∈ α.support := Finsupp.mem_support_iff.2 ha0
    unfold Finsupp.prod
    exact Finset.dvd_prod_of_mem (fun j => z j ^ α j) hi'
  obtain ⟨r, hr⟩ := hdz.trans hprod
  obtain ⟨b, -, hb⟩ := hf α i
  refine ⟨b * ↑U⁻¹ * r, ?_⟩
  rw [hr]
  rw [hau] at hb
  have hUU : (u : Q) * algebraMap B Q (↑U⁻¹ : B) = 1 := by
    rw [← map_natCast (algebraMap B Q), ← map_mul, ← hU, Units.mul_inv, map_one]
  simp only [map_mul, map_pow, map_natCast]
  push_cast at hb
  linear_combination ((p : Q) ^ m * algebraMap B Q (↑U⁻¹ : B) * algebraMap B Q r) * hb -
    (coeff α f * (p : Q) ^ (m + v) * algebraMap B Q r) * hUU

/- English proof (translation)
Take `⟨M, hM⟩` from `term_mem p hunit z hz f hf m`. Use `⟨M, fun n n' hn hnn' => ?_⟩` and prove the remaining obligations. Rewrite using `[psum_eq, psum_eq, ← Finset.sum_sdiff (box_mono hnn'), add_sub_cancel_right]`. Use `AddSubgroup.sum_mem _ fun α hα => ?_` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_lt_of_not_mem_box (Finset.mem_sdiff.1 hα).2`.

Conclude with `hM α i (by omega)`.
-/
theorem cauchy (p : ℕ) [Fact p.Prime] (hunit : ∀ n : ℕ, Nat.Coprime n p → IsUnit (n : B))
    (z : σ → B) (hz : ∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) (f : MvPowerSeries σ Q)
    (hf : DIn (⊤ : Ideal B) f) (m : ℕ) :
    ∃ M : ℕ, ∀ n n' : ℕ, M ≤ n → n ≤ n' → psum z f n' - psum z f n ∈ img B p m := by
  obtain ⟨M, hM⟩ := term_mem p hunit z hz f hf m
  refine ⟨M, fun n n' hn hnn' => ?_⟩
  rw [psum_eq, psum_eq, ← Finset.sum_sdiff (box_mono hnn'), add_sub_cancel_right]
  refine AddSubgroup.sum_mem _ fun α hα => ?_
  obtain ⟨i, hi⟩ := exists_lt_of_not_mem_box (Finset.mem_sdiff.1 hα).2
  exact hM α i (by omega)

end GlobalTheory.QLog.ValEx

namespace GlobalTheory.QLog

open ValEx in

/- English proof (translation)
Introduce `p _ B O Q _ _ _ _ θ hF σ _ _ z hz f hf`. Use `haveI := hF.complete`. Establish `hI : ∀ (k : ℕ) (x : B), x ∈ ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B) ↔ ∃ e, x = (p : B) ^ k * e`. Introduce `k x`. Rewrite using `[Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨e, he⟩; exact ⟨e, by rw [← he, mul_comm]⟩`. Introduce and unpack `⟨e, he⟩; exact ⟨e, by rw [he, mul_comm]⟩`. Use `choose M hM using cauchy p hF.unit_coprime z hz f hf`. Use `set K : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1), M k with hK`.

Establish `hMK : ∀ m, M m ≤ K m` using `fun m => Finset.single_le_sum (fun k _ => Nat.zero_le (M k)) (Finset.mem_range.2 (Nat.lt_succ_self m))`. Establish `hKmono : Monotone K` using `fun a b hab => Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))`. Establish `h0 : ∀ n, psum z f (K n) - psum z f (K 0) ∈ img B p 0` using `fun n => hM 0 (K 0) (K n) (hMK 0) (hKmono (Nat.zero_le n))`. Use `choose b hb using h0`. Establish `hcau : ∀ {k n : ℕ}, k ≤ n → b k ≡ b n [SMOD ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B)]`.

Introduce `k n hkn`. Rewrite using `[SModEq.sub_mem, hI]`. Take `⟨e, he⟩` from `hM k (K k) (K n) (hMK k) (hKmono hkn)`. Use `⟨-e, hF.inj ?_⟩` and prove the remaining obligations. Establish `hbk` using `hb k`.

Establish `hbn` using `hb n`. Simplify using `only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbk hbn he ⊢`. Take the linear combination `hbn - hbk - he`. Take `⟨L, hL⟩` from `IsPrecomplete.prec' b hcau`. Establish `huniq : ∀ q1 q2, HasVal p z f q1 → HasVal p z f q2 → q1 = q2`.

Introduce `q1 q2 h1 h2`. Establish `hd : ∀ m, ∃ e : B, q1 - q2 = algebraMap B Q ((p : B) ^ m * e)`. Introduce `m`. Take `⟨N1, hN1⟩` from `h1 m`. Take `⟨N2, hN2⟩` from `h2 m`.

Take `⟨e1, he1⟩` from `hN1 (max N1 N2) (le_max_left _ _)`. Take `⟨e2, he2⟩` from `hN2 (max N1 N2) (le_max_right _ _)`. Conclude with `⟨e1 - e2, by rw [mul_sub, map_sub, ← he1, ← he2]; ring⟩`. Take `⟨c, hc⟩` from `hd 0`. Establish `hc0 : c = 0`.

Use `IsHausdorff.haus' (I := Ideal.span {(p : B)}) c fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, hI]`. Take `⟨e, he⟩` from `hd n`. Conclude with `⟨e, hF.inj (by rw [← he, hc, pow_zero, one_mul])⟩`. Rewrite using `[← sub_eq_zero, hc, hc0, mul_zero, map_zero]`.

Establish `hq : HasVal p z f (psum z f (K 0) + algebraMap B Q L)` using `fun m => ⟨K m, fun N' hN' => by`. Take `⟨e1, he1⟩` from `(hI m _).1 (SModEq.sub_mem.1 (hL m))`. Take `⟨e2, he2⟩` from `hM m (K m) N' (hMK m) hN'`. Establish `hbm` using `hb m`. Establish `he1'` using `congrArg (algebraMap B Q) he1`.

Use `⟨-e1 - e2, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `psum z f (K 0) + algebraMap B Q L - psum z f N' = _`. Simplify using `only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbm he1' he2 ⊢`. Take the linear combination `-hbm - he1' - he2⟩`. Conclude with `⟨_, hq, fun q' hq' => huniq _ _ hq' hq⟩`.
-/
theorem existsUnique_hasVal_of_dIn : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q]
    [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (σ : Type) [Fintype σ]
    [DecidableEq σ] (z : σ → B), (∀ i, ∃ N : ℕ, (p : B) ∣ z i ^ N) →
    ∀ f : MvPowerSeries σ Q, DIn (⊤ : Ideal B) f → ∃! q : Q, HasVal p z f q := by
  intro p _ B O Q _ _ _ _ θ hF σ _ _ z hz f hf
  haveI := hF.complete
  have hI : ∀ (k : ℕ) (x : B), x ∈ ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B) ↔
      ∃ e, x = (p : B) ^ k * e := by
    intro k x
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
    constructor
    · rintro ⟨e, he⟩; exact ⟨e, by rw [← he, mul_comm]⟩
    · rintro ⟨e, he⟩; exact ⟨e, by rw [he, mul_comm]⟩
  choose M hM using cauchy p hF.unit_coprime z hz f hf
  set K : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1), M k with hK
  have hMK : ∀ m, M m ≤ K m := fun m =>
    Finset.single_le_sum (fun k _ => Nat.zero_le (M k)) (Finset.mem_range.2 (Nat.lt_succ_self m))
  have hKmono : Monotone K := fun a b hab =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hab))
  have h0 : ∀ n, psum z f (K n) - psum z f (K 0) ∈ img B p 0 := fun n =>
    hM 0 (K 0) (K n) (hMK 0) (hKmono (Nat.zero_le n))
  choose b hb using h0
  have hcau : ∀ {k n : ℕ}, k ≤ n →
      b k ≡ b n [SMOD ((Ideal.span {(p : B)}) ^ k • ⊤ : Submodule B B)] := by
    intro k n hkn
    rw [SModEq.sub_mem, hI]
    obtain ⟨e, he⟩ := hM k (K k) (K n) (hMK k) (hKmono hkn)
    refine ⟨-e, hF.inj ?_⟩
    have hbk := hb k
    have hbn := hb n
    simp only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbk hbn he ⊢
    linear_combination hbn - hbk - he
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' b hcau
  have huniq : ∀ q1 q2, HasVal p z f q1 → HasVal p z f q2 → q1 = q2 := by
    intro q1 q2 h1 h2
    have hd : ∀ m, ∃ e : B, q1 - q2 = algebraMap B Q ((p : B) ^ m * e) := by
      intro m
      obtain ⟨N1, hN1⟩ := h1 m
      obtain ⟨N2, hN2⟩ := h2 m
      obtain ⟨e1, he1⟩ := hN1 (max N1 N2) (le_max_left _ _)
      obtain ⟨e2, he2⟩ := hN2 (max N1 N2) (le_max_right _ _)
      exact ⟨e1 - e2, by rw [mul_sub, map_sub, ← he1, ← he2]; ring⟩
    obtain ⟨c, hc⟩ := hd 0
    have hc0 : c = 0 := by
      refine IsHausdorff.haus' (I := Ideal.span {(p : B)}) c fun n => ?_
      rw [SModEq.sub_mem, sub_zero, hI]
      obtain ⟨e, he⟩ := hd n
      exact ⟨e, hF.inj (by rw [← he, hc, pow_zero, one_mul])⟩
    rw [← sub_eq_zero, hc, hc0, mul_zero, map_zero]
  have hq : HasVal p z f (psum z f (K 0) + algebraMap B Q L) := fun m => ⟨K m, fun N' hN' => by
    obtain ⟨e1, he1⟩ := (hI m _).1 (SModEq.sub_mem.1 (hL m))
    obtain ⟨e2, he2⟩ := hM m (K m) N' (hMK m) hN'
    have hbm := hb m
    have he1' := congrArg (algebraMap B Q) he1
    refine ⟨-e1 - e2, ?_⟩
    change psum z f (K 0) + algebraMap B Q L - psum z f N' = _
    simp only [pow_zero, one_mul, map_sub, map_mul, map_neg, map_pow, map_natCast] at hbm he1' he2 ⊢
    linear_combination -hbm - he1' - he2⟩
  exact ⟨_, hq, fun q' hq' => huniq _ _ hq' hq⟩

end GlobalTheory.QLog
