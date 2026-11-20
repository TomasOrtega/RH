import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffOfW
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Filter GlobalTheory.CrysPrism
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CrysPrism.GoodX

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`. Rewrite using `[pow_succ, Nat.succ_mul]`. Conclude with `(Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)`.
-/
theorem pow_factorial_dvd (i m : ℕ) : i.factorial ^ m ∣ (m * i).factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, Nat.succ_mul]
    exact (Nat.mul_dvd_mul_right ih _).trans (Nat.factorial_mul_factorial_dvd_factorial_add _ _)

/- English proof (translation)
Take `⟨m, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hl`. Establish `h1 : i ≤ (m + 1) * i` using `by nlinarith`. Establish `h2` using `Nat.choose_mul_factorial_mul_factorial h1`. Establish `h3 : (m + 1) * i - i = m * i` using `by rw [Nat.succ_mul]; omega`. Rewrite `h2` using `[h3, Nat.choose_mul_right hi]`.

Take `⟨c, hc⟩` from `pow_factorial_dvd i m`. Use `⟨((m + 1) * i - 1).choose (i - 1) * c, ?_⟩` and prove the remaining obligations. Rewrite using `[Nat.succ_eq_add_one, ← h2, hc]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_pow_factorial_dvd (l i : ℕ) (hl : l ≠ 0) (hi : i ≠ 0) :
    i.factorial ^ l * l ∣ (l * i).factorial := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
  have h1 : i ≤ (m + 1) * i := by nlinarith
  have h2 := Nat.choose_mul_factorial_mul_factorial h1
  have h3 : (m + 1) * i - i = m * i := by rw [Nat.succ_mul]; omega
  rw [h3, Nat.choose_mul_right hi] at h2
  obtain ⟨c, hc⟩ := pow_factorial_dvd i m
  refine ⟨((m + 1) * i - 1).choose (i - 1) * c, ?_⟩
  rw [Nat.succ_eq_add_one, ← h2, hc]; ring

/- English proof (translation)
Establish `hv : padicValNat l i.factorial ≤ i - 1`. Establish `h` using `sub_one_mul_padicValNat_factorial (p := l) i`. Establish `h2` using `hl.out.two_le`. Establish `h3 : (l.digits i).sum ≠ 0`. Introduce `h0`.

Establish `hne : l.digits i ≠ []` using `Nat.digits_ne_nil_iff_ne_zero.2 hi`. Conclude with `Nat.getLast_digit_ne_zero l hi (List.sum_eq_zero_iff.1 h0 _ (List.getLast_mem hne))`. Establish `h4 : 1 * padicValNat l i.factorial ≤ (l - 1) * padicValNat l i.factorial` using `Nat.mul_le_mul_right _ (by omega)`. Use linear arithmetic over natural numbers and integers. Take `⟨s, hs⟩ : l ^ padicValNat l i.factorial ∣ i.factorial` from `pow_padicValNat_dvd`.

Establish `hs' : ¬ l ∣ s`. Introduce `h`. Use `pow_succ_padicValNat_not_dvd (p := l) (Nat.factorial_ne_zero i) ?_` and prove the remaining obligations. Rewrite using `[pow_succ]`. Use `conv_rhs => rw [hs]`.

Conclude with `Nat.mul_dvd_mul_left _ h`. Establish `hu : IsUnit (s : ℤ_[l])`. Rewrite using `[PadicInt.isUnit_iff]`. Use `le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hs' ?_)` and prove the remaining obligations. Use `(PadicInt.norm_int_lt_one_iff_dvd (p := l) (s : ℤ)).1 (by simpa using h)` as an intermediate fact.

Conclude with `this` after adjusting the coercions. Take `⟨s', hs2⟩` from `hu.exists_right_inv`. Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le hv`. Use `⟨(l : ℤ_[l]) ^ k * s', ?_⟩` and prove the remaining obligations. Establish `h5 : (i.factorial : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l i.factorial * s` using `by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hs`.

Rewrite using `[hk, pow_add]`. Take the linear combination `((l : ℤ_[l]) ^ k * s') * h5 + ((l : ℤ_[l]) ^ padicValNat l i.factorial * (l : ℤ_[l]) ^ k) * hs2`.
-/
theorem exists_padic (l : ℕ) [hl : Fact l.Prime] (i : ℕ) (hi : i ≠ 0) :
    ∃ d : ℤ_[l], (i.factorial : ℤ_[l]) * d = (l : ℤ_[l]) ^ (i - 1) := by
  have hv : padicValNat l i.factorial ≤ i - 1 := by
    have h := sub_one_mul_padicValNat_factorial (p := l) i
    have h2 := hl.out.two_le
    have h3 : (l.digits i).sum ≠ 0 := by
      intro h0
      have hne : l.digits i ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 hi
      exact Nat.getLast_digit_ne_zero l hi (List.sum_eq_zero_iff.1 h0 _ (List.getLast_mem hne))
    have h4 : 1 * padicValNat l i.factorial ≤ (l - 1) * padicValNat l i.factorial :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨s, hs⟩ : l ^ padicValNat l i.factorial ∣ i.factorial := pow_padicValNat_dvd
  have hs' : ¬ l ∣ s := by
    intro h
    refine pow_succ_padicValNat_not_dvd (p := l) (Nat.factorial_ne_zero i) ?_
    rw [pow_succ]
    conv_rhs => rw [hs]
    exact Nat.mul_dvd_mul_left _ h
  have hu : IsUnit (s : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun h => hs' ?_)
    have := (PadicInt.norm_int_lt_one_iff_dvd (p := l) (s : ℤ)).1 (by simpa using h)
    exact_mod_cast this
  obtain ⟨s', hs2⟩ := hu.exists_right_inv
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hv
  refine ⟨(l : ℤ_[l]) ^ k * s', ?_⟩
  have h5 : (i.factorial : ℤ_[l]) = (l : ℤ_[l]) ^ padicValNat l i.factorial * s := by exact_mod_cast congrArg (Nat.cast : ℕ → ℤ_[l]) hs
  rw [hk, pow_add]
  linear_combination ((l : ℤ_[l]) ^ k * s') * h5 + ((l : ℤ_[l]) ^ padicValNat l i.factorial * (l : ℤ_[l]) ^ k) * hs2

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨Y, hY, hP⟩ : ∃ Y ∈ S, φ x = (l : R) * Y := by`. Use `⟨∑ m ∈ Finset.range l, ((l - 1).descFactorial m : R) * u ^ (l - (m + 1)) * xs (m + 1), ?_, ?_⟩` and prove the remaining obligations. Conclude with `S.sum_mem fun m _ => S.mul_mem (S.mul_mem (natCast_mem S _) (S.pow_mem hu _)) (hxS _)`. Rewrite using `[hφ, add_comm u x, add_pow, Finset.sum_range_succ', Finset.mul_sum]`. Simplify using `only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, add_sub_cancel_right]`.

Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Establish `h : (m + 1).factorial * l.choose (m + 1) = l * (l - 1).descFactorial m`. Rewrite using `[← Nat.descFactorial_eq_factorial_mul_choose]`. Take `⟨n, rfl⟩` from `Nat.exists_eq_succ_of_ne_zero hl`. Conclude with `Nat.succ_descFactorial_succ n m`.

Establish `h' : ((m + 1).factorial : R) * (l.choose (m + 1) : R) = (l : R) * ((l - 1).descFactorial m : R)`. Conclude with `congrArg (Nat.cast : ℕ → R) h` after adjusting the coercions. Rewrite using `[← hxs]`. Take the linear combination `(u ^ (l - (m + 1)) * xs (m + 1)) * h'`. Establish `h1 : φ (xs i) = (l : R) * (d * Y ^ i)`.

Rewrite using `[← sub_eq_zero]`. Apply `htf _ (Nat.factorial_ne_zero i)` to reduce the goal to its premises. Establish `h` using `congrArg φ (hxs i)`. Rewrite `h` using `[map_mul, map_natCast, map_pow, hP, mul_pow]`. Establish `h2 : (l : R) ^ i = l * (l : R) ^ (i - 1)`.

Rewrite using `[← pow_succ']`. Use `congr 1`. Use linear arithmetic over natural numbers and integers. Rewrite `h` using `[h2]`. Take the linear combination `h - ((l : R) * Y ^ i) * hdi`.

Take `⟨c, hc⟩` from `mul_pow_factorial_dvd l i hl hi`. Establish `h2 : xs i ^ l = (l : R) * (c * xs (l * i))`. Rewrite using `[← sub_eq_zero]`. Apply `htf _ (pow_ne_zero l (Nat.factorial_ne_zero i))` to reduce the goal to its premises. Establish `h` using `congrArg (· ^ l) (hxs i)`.

Establish `h3` using `hxs (l * i)`. Rewrite `h3` using `[hc]`. Simplify using `only [mul_pow, ← pow_mul] at h`. Rewrite `h` using `[mul_comm i l]`. Move the coercions through the operations in `at h3 ⊢`.

Take the linear combination `h - h3`. Establish `hm : d * Y ^ i ∈ S` using `S.mul_mem hd (S.pow_mem hY _)`. Use `⟨h1 ▸ S.mul_mem (natCast_mem S _) hm, d * Y ^ i - c * xs (l * i), S.sub_mem hm (S.mul_mem (natCast_mem S _) (hxS _)), ?_⟩` and prove the remaining obligations. Rewrite using `[h1, h2]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem abstract {R : Type} [CommRing R] (htf : ∀ n : ℕ, n ≠ 0 → ∀ x : R, (n : R) * x = 0 → x = 0)
    (S : Subring R) (φ : R →+* R) (l : ℕ) (hl : l ≠ 0) (u x : R) (xs : ℕ → R)
    (hxs : ∀ k : ℕ, (k.factorial : R) * xs k = x ^ k) (hu : u ∈ S) (hxS : ∀ k, xs k ∈ S)
    (hφ : φ x = (u + x) ^ l - u ^ l) (i : ℕ) (hi : i ≠ 0) (d : R) (hd : d ∈ S)
    (hdi : (i.factorial : R) * d = (l : R) ^ (i - 1)) :
    φ (xs i) ∈ S ∧ ∃ B ∈ S, φ (xs i) = xs i ^ l + (l : R) * B := by
  obtain ⟨Y, hY, hP⟩ : ∃ Y ∈ S, φ x = (l : R) * Y := by
    refine ⟨∑ m ∈ Finset.range l, ((l - 1).descFactorial m : R) * u ^ (l - (m + 1)) * xs (m + 1), ?_, ?_⟩
    · exact S.sum_mem fun m _ => S.mul_mem (S.mul_mem (natCast_mem S _) (S.pow_mem hu _)) (hxS _)
    · rw [hφ, add_comm u x, add_pow, Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one,
        add_sub_cancel_right]
      refine Finset.sum_congr rfl fun m _ => ?_
      have h : (m + 1).factorial * l.choose (m + 1) = l * (l - 1).descFactorial m := by
        rw [← Nat.descFactorial_eq_factorial_mul_choose]
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hl
        exact Nat.succ_descFactorial_succ n m
      have h' : ((m + 1).factorial : R) * (l.choose (m + 1) : R) = (l : R) * ((l - 1).descFactorial m : R) := by
        exact_mod_cast congrArg (Nat.cast : ℕ → R) h
      rw [← hxs]
      linear_combination (u ^ (l - (m + 1)) * xs (m + 1)) * h'
  have h1 : φ (xs i) = (l : R) * (d * Y ^ i) := by
    rw [← sub_eq_zero]
    apply htf _ (Nat.factorial_ne_zero i)
    have h := congrArg φ (hxs i)
    rw [map_mul, map_natCast, map_pow, hP, mul_pow] at h
    have h2 : (l : R) ^ i = l * (l : R) ^ (i - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2] at h
    linear_combination h - ((l : R) * Y ^ i) * hdi
  obtain ⟨c, hc⟩ := mul_pow_factorial_dvd l i hl hi
  have h2 : xs i ^ l = (l : R) * (c * xs (l * i)) := by
    rw [← sub_eq_zero]
    apply htf _ (pow_ne_zero l (Nat.factorial_ne_zero i))
    have h := congrArg (· ^ l) (hxs i)
    have h3 := hxs (l * i)
    rw [hc] at h3
    simp only [mul_pow, ← pow_mul] at h
    rw [mul_comm i l] at h
    push_cast at h3 ⊢
    linear_combination h - h3
  have hm : d * Y ^ i ∈ S := S.mul_mem hd (S.pow_mem hY _)
  refine ⟨h1 ▸ S.mul_mem (natCast_mem S _) hm, d * Y ^ i - c * xs (l * i),
    S.sub_mem hm (S.mul_mem (natCast_mem S _) (hxS _)), ?_⟩
  rw [h1, h2]; ring

section Q

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {O : Type} [CommRing O] [Algebra ℤ_[l] O]
  (t : Wq l a →ₐ[ℤ_[l]] O) (K : Type) [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  (e : ℕ)

/- English proof (translation)
Use `⟨fun p => if p = (i, n) then c else 0, funext fun τ => ?_⟩` and prove the remaining obligations. Use extensionality with `j m`. Rewrite using `[coeff_ofW, coeff_C_mul, coeff_X_pow]`. Distinguish the cases in `hj : j = i`. Substitute `hj` using the available equality.

Rewrite using `[if_pos rfl, mul_one, coeff_C_mul, coeff_X_pow]`. Distinguish the cases in `hm : m = n`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hm]`.

Simplify using `[hj]`.
-/
theorem mono_mem (c : Wq l a) (i n : ℕ) :
    (fun τ => C (C (algebraMap O K (emb t τ c) / (dpDen e i n : K)) * X ^ n) * X ^ i :
      ZMod a → K⟦X⟧⟦X⟧) ∈ QSet t K e := by
  refine ⟨fun p => if p = (i, n) then c else 0, funext fun τ => ?_⟩
  ext j m
  rw [coeff_ofW, coeff_C_mul, coeff_X_pow]
  by_cases hj : j = i
  · subst hj
    rw [if_pos rfl, mul_one, coeff_C_mul, coeff_X_pow]
    by_cases hm : m = n
    · subst hm; simp
    · simp [hm]
  · simp [hj]

/- English proof (translation)
Take `⟨v, rfl⟩` from `hx`. Take `⟨w, rfl⟩` from `hy`. Use `⟨v + w, funext fun τ => ?_⟩` and prove the remaining obligations. Use extensionality with `j m`. Simplify using `only [Pi.add_apply, map_add, coeff_ofW, add_div]`.
-/
theorem add_mem {x y : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) (hy : y ∈ QSet t K e) : x + y ∈ QSet t K e := by
  obtain ⟨v, rfl⟩ := hx
  obtain ⟨w, rfl⟩ := hy
  refine ⟨v + w, funext fun τ => ?_⟩
  ext j m
  simp only [Pi.add_apply, map_add, coeff_ofW, add_div]

/- English proof (translation)
Take `⟨v, rfl⟩` from `hx`. Use `⟨-v, funext fun τ => ?_⟩` and prove the remaining obligations. Use extensionality with `j m`. Simplify using `only [Pi.neg_apply, map_neg, coeff_ofW, neg_div]`.
-/
theorem neg_mem {x : ZMod a → K⟦X⟧⟦X⟧} (hx : x ∈ QSet t K e) : -x ∈ QSet t K e := by
  obtain ⟨v, rfl⟩ := hx
  refine ⟨-v, funext fun τ => ?_⟩
  ext j m
  simp only [Pi.neg_apply, map_neg, coeff_ofW, neg_div]

/- English proof (translation)
Use `mono_mem t K e c 0 0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ`. Simplify using `[cstW, dpDen]`.
-/
theorem cstW_mem (c : Wq l a) : cstW t K c ∈ QSet t K e := by
  convert mono_mem t K e c 0 0 using 1
  funext τ
  simp [cstW, dpDen]

/- English proof (translation)
Use `mono_mem t K e 1 i 0 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ`. Simplify using `[xFam, dpDen]`.
-/
theorem xFam_mem (i : ℕ) : xFam a K i ∈ QSet t K e := by
  convert mono_mem t K e 1 i 0 using 1
  funext τ
  simp [xFam, dpDen]

/- English proof (translation)
Use `mono_mem t K e 1 0 1 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `τ`. Establish `h : (1 / e).factorial = 1`. Rewrite using `[Nat.factorial_eq_one]`. Conclude with `Nat.div_le_self _ _`.

Simplify using `[uFam, dpDen, h]`.
-/
theorem uFam_mem : uFam a K ∈ QSet t K e := by
  convert mono_mem t K e 1 0 1 using 1
  funext τ
  have h : (1 / e).factorial = 1 := by
    rw [Nat.factorial_eq_one]; exact Nat.div_le_self _ _
  simp [uFam, dpDen, h]

def qSub (h : ∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) : Subring (ZMod a → K⟦X⟧⟦X⟧) where
  carrier := QSet t K e
  mul_mem' := fun hx hy => h _ hx _ hy
  one_mem' := by
    convert cstW_mem t K e 1 using 1
    funext τ; simp [cstW]
  add_mem' := add_mem t K e
  zero_mem' := by
    convert cstW_mem t K e 0 using 1
    funext τ; simp [cstW]
  neg_mem' := neg_mem t K e

end Q

/- English proof (translation)
Introduce `l hl a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC hX hmul i`. Use `haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective`. Use `⟨xFam_mem t K e i, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hi : i = 0`. Substitute `hi` using the available equality.

Establish `h : xFam a K 0 = 1` using `by funext τ; simp [xFam]`. Rewrite using `[h, map_one]`. Conclude with `⟨(qSub t K e hmul).one_mem, 0, (qSub t K e hmul).zero_mem, by simp⟩`. Take `⟨d, hd⟩` from `exists_padic l i hi`. Use `abstract (fun n hn x hx => tf_pi (natCast_ne_zero_ps (natCast_ne_zero_ps (Nat.cast_ne_zero.2 hn))) x hx) (qSub t K e hmul) (frob2 φ₂) l hl.out.ne_zero (uFam a K) (fun _ => X) (xFam a K) (fun k => ?_) (uFam_mem t K e) (xFam_mem t K e) ?_ i hi (cstW t K (algebraMap ℤ_[l] _ d)) (cst …` and prove the remaining obligations.

Use function extensionality and compare the values at `τ`. Establish `h : (k.factorial : K) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)`. Simplify using `only [Pi.mul_apply, Pi.natCast_apply, Pi.pow_apply, xFam]`. Rewrite using `[← mul_assoc, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_natCast (C : K →+* K⟦X⟧), ← map_mul, ← map_mul, mul_inv_cancel₀ h]`. Simplify using the standard rewrite rules.

Use function extensionality and compare the values at `τ`. Express the relevant statement in the definitionally equal form `φ₂ X = (C X + X) ^ l - C X ^ l`. Rewrite using `[hX, map_pow]`. Use function extensionality and compare the values at `τ`. Establish `h` using `congrArg (fun z => (C (C (algebraMap O K (algebraMap ℤ_[l] O z))) : K⟦X⟧⟦X⟧)) hd`.

Simplify using `only [map_mul, map_natCast, map_pow] at h`. Simplify `h` using `[cstW]`.
-/
theorem xFam_mem_GoodSet : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O), ∀ (φ₂ : K⟦X⟧⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ f : K⟦X⟧, φ₂ (C f) = C (frob K l f)) → φ₂ X = (C X + X) ^ l - C (X ^ l) → (∀ x ∈ QSet t K e, ∀ y ∈ QSet t K e, x * y ∈ QSet t K e) → ∀ i : ℕ, xFam a K i ∈ GoodSet t e φ₂ := by
  intro l hl a e _ _ O K _ _ _ _ _ _ _ t φ₂ hC hX hmul i
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine ⟨xFam_mem t K e i, ?_⟩
  by_cases hi : i = 0
  · subst hi
    have h : xFam a K 0 = 1 := by funext τ; simp [xFam]
    rw [h, map_one]
    exact ⟨(qSub t K e hmul).one_mem, 0, (qSub t K e hmul).zero_mem, by simp⟩
  obtain ⟨d, hd⟩ := exists_padic l i hi
  refine abstract (fun n hn x hx => tf_pi (natCast_ne_zero_ps (natCast_ne_zero_ps (Nat.cast_ne_zero.2 hn))) x hx)
    (qSub t K e hmul) (frob2 φ₂) l hl.out.ne_zero (uFam a K) (fun _ => X) (xFam a K) (fun k => ?_)
    (uFam_mem t K e) (xFam_mem t K e) ?_ i hi (cstW t K (algebraMap ℤ_[l] _ d)) (cstW_mem t K e _) ?_
  · funext τ
    have h : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)
    simp only [Pi.mul_apply, Pi.natCast_apply, Pi.pow_apply, xFam]
    rw [← mul_assoc, ← map_natCast (C : K⟦X⟧ →+* K⟦X⟧⟦X⟧), ← map_natCast (C : K →+* K⟦X⟧), ← map_mul, ← map_mul,
      mul_inv_cancel₀ h]
    simp
  · funext τ
    change φ₂ X = (C X + X) ^ l - C X ^ l
    rw [hX, map_pow]
  · funext τ
    have h := congrArg (fun z => (C (C (algebraMap O K (algebraMap ℤ_[l] O z))) : K⟦X⟧⟦X⟧)) hd
    simp only [map_mul, map_natCast, map_pow] at h
    simpa [cstW] using h

end GlobalTheory.CrysPrism.GoodX
