import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists

noncomputable section

open Polynomial

namespace GlobalTheory.K5.QRoot

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

/- English proof (translation)
The claim follows from `pow_pos (by exact_mod_cast hp.out.pos) n`.
-/
theorem pn_pos : (0 : ℤ) < (p : ℤ) ^ n := pow_pos (by exact_mod_cast hp.out.pos) n

def mulN : ℤ →+ ℤ := AddMonoidHom.mulLeft ((p : ℤ) ^ n)

/- English proof (translation)
Introduce `a b h` and use `mul_left_cancel₀ (pn_pos p n).ne' h`.
-/
theorem mulN_inj : Function.Injective (mulN p n) := fun a b h =>
  mul_left_cancel₀ (pn_pos p n).ne' h

/- English proof (translation)
The claim follows from `mul_le_mul_iff_of_pos_left (pn_pos p n)`.
-/
theorem mulN_le (a b : ℤ) : mulN p n a ≤ mulN p n b ↔ a ≤ b :=
  mul_le_mul_iff_of_pos_left (pn_pos p n)

def vL : Lau p →+* Lau p := HahnSeries.embDomainRingHom (mulN p n) (mulN_inj p n) (mulN_le p n)

/- English proof (translation)
Use `show (HahnSeries.embDomain _ a).coeff (mulN p n i) = _`. Conclude with `HahnSeries.embDomain_coeff`.
-/
theorem vL_coeff (a : Lau p) (i : ℤ) : (vL p n a).coeff ((p : ℤ) ^ n * i) = a.coeff i := by
  show (HahnSeries.embDomain _ a).coeff (mulN p n i) = _
  exact HahnSeries.embDomain_coeff

/- English proof (translation)
Apply `HahnSeries.embDomain_notin_image_support` to reduce the goal to its premises. Introduce and unpack `⟨i, -, hi⟩`. Conclude with `h ⟨i, hi.symm⟩`.
-/
theorem vL_coeff_of_not_dvd (a : Lau p) (r : ℤ) (h : ¬ (p : ℤ) ^ n ∣ r) : (vL p n a).coeff r = 0 := by
  apply HahnSeries.embDomain_notin_image_support
  rintro ⟨i, -, hi⟩
  exact h ⟨i, hi.symm⟩

/- English proof (translation)
Use `show HahnSeries.embDomain _ _ = _`. Rewrite using `[HahnSeries.embDomain_single]`. Both sides reduce to the same expression.
-/
theorem vL_single (k : ℤ) (c : ℤ_[p]) : vL p n (HahnSeries.single k c) = HahnSeries.single ((p : ℤ) ^ n * k) c := by
  show HahnSeries.embDomain _ _ = _
  rw [HahnSeries.embDomain_single]; rfl

/- English proof (translation)
Distinguish the cases in `ha : a = 0`. Substitute `ha; exact ⟨0, fun i hi => by simp at hi⟩` using the available equality. Use `⟨min 0 (a.order - j), fun i hi => ?_⟩` and prove the remaining obligations. Establish `h1` using `HahnSeries.order_le_of_coeff_ne_zero hi`. Establish `h2` using `pn_pos p n`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `h3 : i < 0` using `lt_of_lt_of_le h (min_le_left _ _)`. Establish `h4 : i < a.order - j` using `lt_of_lt_of_le h (min_le_right _ _)`. Establish `h5 : (p : ℤ) ^ n * i ≤ i` using `by nlinarith`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem bddBelow_support_primePowerComponent_coeff (a : Lau p) (j : ℤ) : BddBelow (Function.support (fun i : ℤ => a.coeff ((p : ℤ) ^ n * i + j))) := by
  by_cases ha : a = 0
  · subst ha; exact ⟨0, fun i hi => by simp at hi⟩
  · refine ⟨min 0 (a.order - j), fun i hi => ?_⟩
    have h1 := HahnSeries.order_le_of_coeff_ne_zero hi
    have h2 := pn_pos p n
    by_contra h
    push_neg at h
    have h3 : i < 0 := lt_of_lt_of_le h (min_le_left _ _)
    have h4 : i < a.order - j := lt_of_lt_of_le h (min_le_right _ _)
    have h5 : (p : ℤ) ^ n * i ≤ i := by nlinarith
    linarith

def dL (j : ℤ) (a : Lau p) : Lau p :=
  HahnSeries.ofSuppBddBelow (fun i : ℤ => a.coeff ((p : ℤ) ^ n * i + j)) (bddBelow_support_primePowerComponent_coeff p n a j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dL_coeff (j : ℤ) (a : Lau p) (i : ℤ) : (dL p n j a).coeff i = a.coeff ((p : ℤ) ^ n * i + j) := rfl

/- English proof (translation)
Use extensionality with `i`. Simplify using `[dL_coeff]`.
-/
theorem dL_sub (j : ℤ) (a b : Lau p) : dL p n j (a - b) = dL p n j a - dL p n j b := by
  ext i; simp [dL_coeff]

/- English proof (translation)
Establish `: r = (r - j) + j` using `by ring`. Use `conv_lhs => rw [this]`. Rewrite using `[HahnSeries.coeff_mul_single_add, mul_one]`.
-/
theorem coeff_mul_qj (x : Lau p) (j r : ℤ) : (x * HahnSeries.single j (1 : ℤ_[p])).coeff r = x.coeff (r - j) := by
  have : r = (r - j) + j := by ring
  conv_lhs => rw [this]
  rw [HahnSeries.coeff_mul_single_add, mul_one]

/- English proof (translation)
Use extensionality with `r`. Rewrite using `[HahnSeries.coeff_sum]`. Simplify using `only [coeff_mul_qj]`. Establish `hN` using `pn_pos p n`. Use `set j0 : ℕ := (r % ((p : ℤ) ^ n)).toNat with hj0`.

Establish `hj0' : (j0 : ℤ) = r % ((p : ℤ) ^ n)` using `Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')`. Establish `hj0N : j0 < p ^ n`. Use `Int.emod_lt_of_pos r hN` as an intermediate fact. Establish `h' : (j0 : ℤ) < ((p ^ n : ℕ) : ℤ)` using `by push_cast; omega`. Conclude with `h'` after adjusting the coercions.

Rewrite using `[Finset.sum_eq_single j0]`. Establish `: r - (j0 : ℤ) = (p : ℤ) ^ n * (r / (p : ℤ) ^ n)`. Rewrite using `[hj0', Int.emod_def]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, vL_coeff, dL_coeff, ← this]`.

Put the polynomial expressions in normal form. Introduce `j hj hne`. Apply `vL_coeff_of_not_dvd` to reduce the goal to its premises. Introduce and unpack `⟨m, hm⟩`. Apply `hne` to reduce the goal to its premises.

Establish `hjN : (j : ℤ) < (p : ℤ) ^ n` using `by exact_mod_cast (Finset.mem_range.1 hj)`. Establish `hr : r = (j : ℤ) + (p : ℤ) ^ n * m` using `by linarith`. Establish `: r % ((p : ℤ) ^ n) = (j : ℤ)`. Rewrite using `[hr, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) hjN]`. Use linear arithmetic over natural numbers and integers.

Introduce `h`. Conclude with `absurd (Finset.mem_range.2 hj0N) h`.
-/
theorem decomp (a : Lau p) :
    a = ∑ j ∈ Finset.range (p ^ n), vL p n (dL p n j a) * HahnSeries.single (j : ℤ) (1 : ℤ_[p]) := by
  ext r
  rw [HahnSeries.coeff_sum]
  simp only [coeff_mul_qj]
  have hN := pn_pos p n
  set j0 : ℕ := (r % ((p : ℤ) ^ n)).toNat with hj0
  have hj0' : (j0 : ℤ) = r % ((p : ℤ) ^ n) := Int.toNat_of_nonneg (Int.emod_nonneg _ hN.ne')
  have hj0N : j0 < p ^ n := by
    have := Int.emod_lt_of_pos r hN
    have h' : (j0 : ℤ) < ((p ^ n : ℕ) : ℤ) := by push_cast; omega
    exact_mod_cast h'
  rw [Finset.sum_eq_single j0]
  · have : r - (j0 : ℤ) = (p : ℤ) ^ n * (r / (p : ℤ) ^ n) := by
      rw [hj0', Int.emod_def]; ring
    rw [this, vL_coeff, dL_coeff, ← this]; ring_nf
  · intro j hj hne
    apply vL_coeff_of_not_dvd
    rintro ⟨m, hm⟩
    apply hne
    have hjN : (j : ℤ) < (p : ℤ) ^ n := by exact_mod_cast (Finset.mem_range.1 hj)
    have hr : r = (j : ℤ) + (p : ℤ) ^ n * m := by linarith
    have : r % ((p : ℤ) ^ n) = (j : ℤ) := by
      rw [hr, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) hjN]
    omega
  · intro h; exact absurd (Finset.mem_range.2 hj0N) h

end GlobalTheory.K5.QRoot

namespace GlobalTheory.K5.QRoot

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

/- English proof (translation)
Use extensionality with `i`. Rewrite using `[dL_coeff, HahnSeries.coeff_sum]`. Simplify using `only [coeff_mul_qj]`. Establish `hN` using `pn_pos p n`. Rewrite using `[Finset.sum_eq_single j]`.

Rewrite using `[show (p : ℤ) ^ n * i + (j : ℤ) - (j : ℤ) = (p : ℤ) ^ n * i by ring, vL_coeff]`. Introduce `k hk hne`. Apply `vL_coeff_of_not_dvd` to reduce the goal to its premises. Introduce and unpack `⟨m, hm⟩`. Apply `hne` to reduce the goal to its premises.

Establish `hkN : (k : ℤ) < (p : ℤ) ^ n` using `by exact_mod_cast (Finset.mem_range.1 hk)`. Establish `hjN : (j : ℤ) < (p : ℤ) ^ n` using `by exact_mod_cast hj`. Establish `h1 : ((j : ℤ) - k) = (p : ℤ) ^ n * (m - i)` using `by linarith`. Establish `h2 : m - i = 0`. Assume the negation of the conclusion as `h0`.

Break down `lt_or_gt_of_ne h0 with h0 | h0` into its components or cases. Establish `: (p : ℤ) ^ n * (m - i) ≤ -(p : ℤ) ^ n` using `by nlinarith`. Use linear arithmetic over natural numbers and integers. Establish `: (p : ℤ) ^ n ≤ (p : ℤ) ^ n * (m - i)` using `by nlinarith`. Use linear arithmetic over natural numbers and integers.

Rewrite `h1` using `[h2, mul_zero]`. Use linear arithmetic over natural numbers and integers. Introduce `h`. Conclude with `absurd (Finset.mem_range.2 hj) h`.
-/
theorem dL_sum (b : ℕ → Lau p) (j : ℕ) (hj : j < p ^ n) :
    dL p n j (∑ k ∈ Finset.range (p ^ n), vL p n (b k) * HahnSeries.single (k : ℤ) (1 : ℤ_[p])) = b j := by
  ext i
  rw [dL_coeff, HahnSeries.coeff_sum]
  simp only [coeff_mul_qj]
  have hN := pn_pos p n
  rw [Finset.sum_eq_single j]
  · rw [show (p : ℤ) ^ n * i + (j : ℤ) - (j : ℤ) = (p : ℤ) ^ n * i by ring, vL_coeff]
  · intro k hk hne
    apply vL_coeff_of_not_dvd
    rintro ⟨m, hm⟩
    apply hne
    have hkN : (k : ℤ) < (p : ℤ) ^ n := by exact_mod_cast (Finset.mem_range.1 hk)
    have hjN : (j : ℤ) < (p : ℤ) ^ n := by exact_mod_cast hj
    have h1 : ((j : ℤ) - k) = (p : ℤ) ^ n * (m - i) := by linarith
    have h2 : m - i = 0 := by
      by_contra h0
      rcases lt_or_gt_of_ne h0 with h0 | h0
      · have : (p : ℤ) ^ n * (m - i) ≤ -(p : ℤ) ^ n := by nlinarith
        omega
      · have : (p : ℤ) ^ n ≤ (p : ℤ) ^ n * (m - i) := by nlinarith
        omega
    rw [h2, mul_zero] at h1
    omega
  · intro h; exact absurd (Finset.mem_range.2 hj) h

/- English proof (translation)
Rewrite `h`, the goal using `[GlobalTheory.K5.Basic.natCast_pow_dvd_iff]`. Introduce `i`. Conclude with `h _`.
-/
theorem dvd_dL (k : ℕ) (j : ℤ) (a : Lau p) (h : (p : Lau p) ^ k ∣ a) : (p : Lau p) ^ k ∣ dL p n j a := by
  rw [GlobalTheory.K5.Basic.natCast_pow_dvd_iff] at h ⊢
  intro i
  exact h _

/- English proof (translation)
Introduce `x hx`. Rewrite using `[Ideal.mem_comap]`. Rewrite `hx`, the goal using `[GlobalTheory.K5.Basic.mem_pI_pow]`. Take `⟨c, rfl⟩` from `hx`. Conclude with `⟨vL p n c, by rw [map_mul, map_pow, map_natCast]⟩`.
-/
theorem vL_pI_le (k : ℕ) : pI p ^ k ≤ (pI p ^ k).comap (vL p n) := by
  intro x hx
  rw [Ideal.mem_comap]
  rw [GlobalTheory.K5.Basic.mem_pI_pow] at hx ⊢
  obtain ⟨c, rfl⟩ := hx
  exact ⟨vL p n c, by rw [map_mul, map_pow, map_natCast]⟩

def vLk (k : ℕ) : O0 p →+* Lau p ⧸ pI p ^ k :=
  (Ideal.quotientMap (pI p ^ k) (vL p n) (vL_pI_le p n k)).comp (AdicCompletion.evalₐ (pI p) k).toRingHom

/- English proof (translation)
Take `⟨x, rfl⟩` from `AdicCompletion.mk_surjective (pI p) (Lau p) x`. Simplify using `only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]`. Rewrite using `[Ideal.Quotient.eq, GlobalTheory.K5.Basic.mem_pI_pow]`. Use `GlobalTheory.K5.Basic.seq_sub_dvd p x hle` as an intermediate fact. Conclude with `this`.
-/
theorem evalₐ_factorPow {k m : ℕ} (hle : k ≤ m) (x : O0 p) :
    Ideal.Quotient.factorPow (pI p) hle (AdicCompletion.evalₐ (pI p) m x) = AdicCompletion.evalₐ (pI p) k x := by
  obtain ⟨x, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) x
  simp only [AdicCompletion.evalₐ_mk, Ideal.Quotient.factorPow, Ideal.Quotient.factor_mk]
  rw [Ideal.Quotient.eq, GlobalTheory.K5.Basic.mem_pI_pow]
  have := GlobalTheory.K5.Basic.seq_sub_dvd p x hle
  exact this

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [vLk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`. Rewrite using `[← evalₐ_factorPow p hle x]`. Take `⟨y, hy⟩` from `Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (pI p) m x)`. Rewrite using `[← hy]`.

Simplify using `[Ideal.Quotient.factorPow, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]`.
-/
theorem vLk_compat {k m : ℕ} (hle : k ≤ m) :
    (Ideal.Quotient.factorPow (pI p) hle).comp (vLk p n m) = vLk p n k := by
  ext x
  simp only [vLk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← evalₐ_factorPow p hle x]
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ (pI p) m x)
  rw [← hy]
  simp [Ideal.Quotient.factorPow, Ideal.quotientMap_mk, Ideal.Quotient.factor_mk]

def vO : O0 p →+* O0 p := AdicCompletion.liftRingHom (pI p) (vLk p n) (fun hle => vLk_compat p n hle)

/- English proof (translation)
Rewrite using `[vO, AdicCompletion.evalₐ_liftRingHom]`. Simplify using `only [vLk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hy, Ideal.quotientMap_mk]`.
-/
theorem evalₐ_vO (k : ℕ) (x : O0 p) (y : Lau p) (hy : AdicCompletion.evalₐ (pI p) k x = Ideal.Quotient.mk _ y) :
    AdicCompletion.evalₐ (pI p) k (vO p n x) = Ideal.Quotient.mk _ (vL p n y) := by
  rw [vO, AdicCompletion.evalₐ_liftRingHom]
  simp only [vLk, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hy, Ideal.quotientMap_mk]

/- English proof (translation)
Rewrite using `[AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem evalₐ_alg (k : ℕ) (y : Lau p) :
    AdicCompletion.evalₐ (pI p) k (algebraMap (Lau p) (O0 p) y) = Ideal.Quotient.mk _ y := by
  rw [AlgHom.commutes]; rfl

/- English proof (translation)
The claim follows from `AdicCompletion.ext_evalₐ fun k => by rw [evalₐ_vO p n k _ y (evalₐ_alg p k y), evalₐ_alg]`.
-/
theorem vO_alg (y : Lau p) : vO p n (algebraMap (Lau p) (O0 p) y) = algebraMap (Lau p) (O0 p) (vL p n y) :=
  AdicCompletion.ext_evalₐ fun k => by rw [evalₐ_vO p n k _ y (evalₐ_alg p k y), evalₐ_alg]

/- English proof (translation)
Rewrite using `[qO, ← map_pow, HahnSeries.single_pow, one_pow]`. Simplify using the standard rewrite rules.
-/
theorem qO_pow (j : ℕ) : qO p ^ j = algebraMap (Lau p) (O0 p) (HahnSeries.single (j : ℤ) (1 : ℤ_[p])) := by
  rw [qO, ← map_pow, HahnSeries.single_pow, one_pow]; simp

/- English proof (translation)
Rewrite using `[qO, vO_alg, vL_single, ← map_pow, HahnSeries.single_pow, one_pow]`. Use `congr 2`.
-/
theorem vO_qO : vO p n (qO p) = qO p ^ (p ^ n) := by
  rw [qO, vO_alg, vL_single, ← map_pow, HahnSeries.single_pow, one_pow]; congr 2

end GlobalTheory.K5.QRoot

namespace GlobalTheory.K5.QRoot

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

/- English proof (translation)
Rewrite using `[map_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, evalₐ_vO p n k _ _ (hy j), qO_pow, evalₐ_alg]`.
-/
theorem evalₐ_sum_eq (c : ℕ → O0 p) (k : ℕ) (y : ℕ → Lau p)
    (hy : ∀ j, AdicCompletion.evalₐ (pI p) k (c j) = Ideal.Quotient.mk _ (y j)) :
    AdicCompletion.evalₐ (pI p) k (∑ j ∈ Finset.range (p ^ n), vO p n (c j) * qO p ^ j) =
      Ideal.Quotient.mk _ (∑ j ∈ Finset.range (p ^ n), vL p n (y j) * HahnSeries.single (j : ℤ) (1 : ℤ_[p])) := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, evalₐ_vO p n k _ _ (hy j), qO_pow, evalₐ_alg]

/- English proof (translation)
Apply `AdicCompletion.ext_evalₐ` to reduce the goal to its premises. Introduce `k`. Use `choose y hy using fun j => Ideal.Quotient.mk_surjective (I := pI p ^ k) (AdicCompletion.evalₐ (pI p) k (c j))`. Establish `h1` using `evalₐ_sum_eq p n c k y (fun j => (hy j).symm)`. Rewrite `h1` using `[h, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.K5.Basic.mem_pI_pow]`.

Establish `h2` using `dvd_dL p n k j _ h1`. Rewrite `h2` using `[dL_sum p n y j hj]`. Rewrite using `[← hy j, map_zero, Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.K5.Basic.mem_pI_pow]`. Conclude with `h2`.
-/
theorem uniq (c : ℕ → O0 p) (h : ∑ j ∈ Finset.range (p ^ n), vO p n (c j) * qO p ^ j = 0) (j : ℕ) (hj : j < p ^ n) :
    c j = 0 := by
  apply AdicCompletion.ext_evalₐ
  intro k
  choose y hy using fun j => Ideal.Quotient.mk_surjective (I := pI p ^ k) (AdicCompletion.evalₐ (pI p) k (c j))
  have h1 := evalₐ_sum_eq p n c k y (fun j => (hy j).symm)
  rw [h, map_zero, eq_comm, Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.K5.Basic.mem_pI_pow] at h1
  have h2 := dvd_dL p n k j _ h1
  rw [dL_sum p n y j hj] at h2
  rw [← hy j, map_zero, Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.K5.Basic.mem_pI_pow]
  exact h2

def seqD (j : ℤ) (s : AdicCompletion.AdicCauchySequence (pI p) (Lau p)) :
    AdicCompletion.AdicCauchySequence (pI p) (Lau p) :=
  ⟨fun k => dL p n j (s.1 k), fun {m k} hmk => by
    rw [SModEq.sub_mem, ← dL_sub]
    have h1 := GlobalTheory.K5.Basic.seq_sub_dvd p s hmk
    have h2 : dL p n j (s.1 m - s.1 k) ∈ pI p ^ m := by
      rw [GlobalTheory.K5.Basic.mem_pI_pow]
      exact dvd_dL p n m j _ (dvd_sub_comm.1 h1)
    simpa using h2⟩

/- English proof (translation)
Take `⟨s, rfl⟩` from `AdicCompletion.mk_surjective (pI p) (Lau p) x`. Use `⟨fun j => AdicCompletion.mk (pI p) (Lau p) (seqD p n j s), AdicCompletion.ext_evalₐ fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[evalₐ_sum_eq p n _ k (fun j => dL p n j (s.1 k)) (fun j => by rw [AdicCompletion.evalₐ_mk]; rfl), AdicCompletion.evalₐ_mk, ← decomp]`.
-/
theorem exist (x : O0 p) : ∃ c : ℕ → O0 p, x = ∑ j ∈ Finset.range (p ^ n), vO p n (c j) * qO p ^ j := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective (pI p) (Lau p) x
  refine ⟨fun j => AdicCompletion.mk (pI p) (Lau p) (seqD p n j s), AdicCompletion.ext_evalₐ fun k => ?_⟩
  rw [evalₐ_sum_eq p n _ k (fun j => dL p n j (s.1 k)) (fun j => by rw [AdicCompletion.evalₐ_mk]; rfl),
    AdicCompletion.evalₐ_mk, ← decomp]

end GlobalTheory.K5.QRoot

namespace GlobalTheory.K5.QRoot

variable (p : ℕ) [hp : Fact p.Prime] (n : ℕ)

def fY : Polynomial (O0 p) := X ^ (p ^ n) - C (qO p)

/- English proof (translation)
The claim follows from `monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero)`.
-/
theorem fY_monic : (fY p n).Monic := monic_X_pow_sub_C _ (pow_ne_zero _ hp.out.ne_zero)

/- English proof (translation)
The claim follows from `natDegree_X_pow_sub_C`.
-/
theorem fY_natDegree : (fY p n).natDegree = p ^ n := natDegree_X_pow_sub_C

def phiInv : AdjoinRoot (fY p n) →+* O0 p :=
  AdjoinRoot.lift (vO p n) (qO p) (by simp [fY, vO_qO])

/- English proof (translation)
Establish `hf` using `fY_monic p n`. Establish `h1 : AdjoinRoot.mk (fY p n) g = AdjoinRoot.mk (fY p n) (g %ₘ fY p n)`. Rewrite using `[AdjoinRoot.mk_eq_mk]`. Use `⟨g /ₘ fY p n, ?_⟩` and prove the remaining obligations. Use `modByMonic_add_div g (fY p n)` as an intermediate fact.

Take the linear combination `-this`. Establish `hdeg : (g %ₘ fY p n).natDegree < p ^ n`. Rewrite using `[← fY_natDegree p n]`. Apply `natDegree_modByMonic_lt g hf` to reduce the goal to its premises. Introduce `h1`.

Use `fY_natDegree p n` as an intermediate fact. Rewrite `this` using `[h1, natDegree_one]`. Conclude with `(pow_ne_zero n hp.out.ne_zero) this.symm`. Rewrite using `[h1, phiInv, AdjoinRoot.lift_mk, eval₂_eq_sum_range' _ hdeg]`.
-/
theorem phiInv_mk_eq (g : Polynomial (O0 p)) :
    phiInv p n (AdjoinRoot.mk (fY p n) g) =
      ∑ j ∈ Finset.range (p ^ n), vO p n ((g %ₘ fY p n).coeff j) * qO p ^ j := by
  have hf := fY_monic p n
  have h1 : AdjoinRoot.mk (fY p n) g = AdjoinRoot.mk (fY p n) (g %ₘ fY p n) := by
    rw [AdjoinRoot.mk_eq_mk]
    refine ⟨g /ₘ fY p n, ?_⟩
    have := modByMonic_add_div g (fY p n)
    linear_combination -this
  have hdeg : (g %ₘ fY p n).natDegree < p ^ n := by
    rw [← fY_natDegree p n]
    apply natDegree_modByMonic_lt g hf
    intro h1
    have := fY_natDegree p n
    rw [h1, natDegree_one] at this
    exact (pow_ne_zero n hp.out.ne_zero) this.symm
  rw [h1, phiInv, AdjoinRoot.lift_mk, eval₂_eq_sum_range' _ hdeg]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨g, rfl⟩` from `AdjoinRoot.mk_surjective x`. Rewrite `hx` using `[phiInv_mk_eq]`.

Establish `hc` using `uniq p n (fun j => (g %ₘ fY p n).coeff j) hx`. Establish `hdeg : (g %ₘ fY p n).natDegree < p ^ n`. Rewrite using `[← fY_natDegree p n]`. Apply `natDegree_modByMonic_lt g (fY_monic p n)` to reduce the goal to its premises. Introduce `h1`.

Use `fY_natDegree p n` as an intermediate fact. Rewrite `this` using `[h1, natDegree_one]`. Conclude with `(pow_ne_zero n hp.out.ne_zero) this.symm`. Establish `h0 : g %ₘ fY p n = 0`. Use `Polynomial.ext fun j => ?_` and prove the remaining obligations.

Rewrite using `[coeff_zero]`. Distinguish the cases in `hj : j < p ^ n`. Conclude with `hc j hj`. Conclude with `coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (not_lt.1 hj))`. Rewrite using `[AdjoinRoot.mk_eq_zero]`.

Conclude with `(modByMonic_eq_zero_iff_dvd (fY_monic p n)).1 h0`. Introduce `y`. Take `⟨c, hc⟩` from `exist p n y`. Use `⟨∑ j ∈ Finset.range (p ^ n), AdjoinRoot.of (fY p n) (c j) * AdjoinRoot.root (fY p n) ^ j, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_pow, phiInv, AdjoinRoot.lift_of, AdjoinRoot.lift_root]`.
-/
theorem phiInv_bij : Function.Bijective (phiInv p n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective x
    rw [phiInv_mk_eq] at hx
    have hc := uniq p n (fun j => (g %ₘ fY p n).coeff j) hx
    have hdeg : (g %ₘ fY p n).natDegree < p ^ n := by
      rw [← fY_natDegree p n]
      apply natDegree_modByMonic_lt g (fY_monic p n)
      intro h1
      have := fY_natDegree p n
      rw [h1, natDegree_one] at this
      exact (pow_ne_zero n hp.out.ne_zero) this.symm
    have h0 : g %ₘ fY p n = 0 := by
      refine Polynomial.ext fun j => ?_
      rw [coeff_zero]
      by_cases hj : j < p ^ n
      · exact hc j hj
      · exact coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le hdeg (not_lt.1 hj))
    rw [AdjoinRoot.mk_eq_zero]
    exact (modByMonic_eq_zero_iff_dvd (fY_monic p n)).1 h0
  · intro y
    obtain ⟨c, hc⟩ := exist p n y
    refine ⟨∑ j ∈ Finset.range (p ^ n), AdjoinRoot.of (fY p n) (c j) * AdjoinRoot.root (fY p n) ^ j, ?_⟩
    rw [hc, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_pow, phiInv, AdjoinRoot.lift_of, AdjoinRoot.lift_root]

end GlobalTheory.K5.QRoot

namespace GlobalTheory.Glue

open GlobalTheory.K5 GlobalTheory.K5.QRoot

/- English proof (translation)
Introduce `p _ Ω _ _ hC T n`. Set `e : AdjoinRoot (fY p n) ≃+* O0 p` to `RingEquiv.ofBijective (phiInv p n) (phiInv_bij p n)`. Set `ι : AdjoinRoot (fY p n) →+* Ω` to `AdjoinRoot.lift (algebraMap (O0 p) Ω) (T.qq n) (by simp [fY, GlobalTheory.K5.Basic.qq_pow])`. Use `haveI : IsDomain (AdjoinRoot (fY p n)) := Function.Injective.isDomain (phiInv p n) (phiInv_bij p n).1`. Use `haveI : Module.Finite (O0 p) (AdjoinRoot (fY p n)) := (AdjoinRoot.powerBasis' (fY_monic p n)).finite`.

Establish `hιinj : Function.Injective ι`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Assume the negation of the conclusion as `hne`. Establish `hI` using `Ideal.comap_ne_bot_of_integral_mem (R := O0 p) hne (show x ∈ RingHom.ker ι from hx) (Algebra.IsIntegral.isIntegral x)`.

Apply `hI` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `a ha`. Rewrite `ha` using `[Ideal.mem_comap, RingHom.mem_ker]`. Rewrite using `[Ideal.mem_bot]`.

Apply `hC.inj` to reduce the goal to its premises. Rewrite using `[map_zero, ← ha]`. Conclude with `(AdjoinRoot.lift_of _).symm`. Use `⟨ι.comp e.symm.toRingHom, ⟨?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `hιinj.comp e.symm.injective`.

Use `show ι (e.symm (qO p)) = T.qq n`. Establish `: e.symm (qO p) = AdjoinRoot.root (fY p n)`. Rewrite using `[RingEquiv.symm_apply_eq]`. Use `show qO p = phiInv p n (AdjoinRoot.root _)`. Rewrite using `[phiInv, AdjoinRoot.lift_root]`.

Rewrite using `[this]`. Conclude with `AdjoinRoot.lift_root _`. Introduce `a b hb hb0`. Establish `hbv : b = vL p n a`. Use extensionality with `r`.

Distinguish the cases in `hr : (p : ℤ) ^ n ∣ r`. Take `⟨i, rfl⟩` from `hr`. Rewrite using `[hb i, vL_coeff]`. Rewrite using `[hb0 r hr, vL_coeff_of_not_dvd p n a r hr]`. Use `show ι (e.symm _) = _`.

Establish `: e.symm (algebraMap (Lau p) (O0 p) b) = AdjoinRoot.of _ (algebraMap (Lau p) (O0 p) a)`. Rewrite using `[RingEquiv.symm_apply_eq, hbv, ← vO_alg]`. Use `show _ = phiInv p n (AdjoinRoot.of _ _)`. Rewrite using `[phiInv, AdjoinRoot.lift_of]`. Rewrite using `[this]`.

Conclude with `AdjoinRoot.lift_of _`. Use extensionality with `y`. Simplify using `only [RingHom.mem_range, Subalgebra.mem_toSubring, Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`.

Take `⟨g, hg⟩` from `AdjoinRoot.mk_surjective (e.symm x)`. Use `⟨g, ?_⟩` and prove the remaining obligations. Use `show _ = ι (e.symm x)`. Rewrite using `[← hg, AdjoinRoot.lift_mk]`. Both sides reduce to the same expression.

Introduce and unpack `⟨g, rfl⟩`. Use `⟨e (AdjoinRoot.mk _ g), ?_⟩` and prove the remaining obligations. Use `show ι (e.symm (e _)) = _`. Rewrite using `[e.symm_apply_apply, AdjoinRoot.lift_mk]`. Both sides reduce to the same expression.
-/
theorem exists_isReb : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∃ ψ : O0 p →+* Ω, IsReb T n ψ := by
  intro p _ Ω _ _ hC T n
  let e : AdjoinRoot (fY p n) ≃+* O0 p := RingEquiv.ofBijective (phiInv p n) (phiInv_bij p n)
  let ι : AdjoinRoot (fY p n) →+* Ω :=
    AdjoinRoot.lift (algebraMap (O0 p) Ω) (T.qq n) (by simp [fY, GlobalTheory.K5.Basic.qq_pow])
  haveI : IsDomain (AdjoinRoot (fY p n)) := Function.Injective.isDomain (phiInv p n) (phiInv_bij p n).1
  haveI : Module.Finite (O0 p) (AdjoinRoot (fY p n)) := (AdjoinRoot.powerBasis' (fY_monic p n)).finite
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hne
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := O0 p) hne (show x ∈ RingHom.ker ι from hx)
      (Algebra.IsIntegral.isIntegral x)
    apply hI
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    rw [Ideal.mem_bot]
    apply hC.inj
    rw [map_zero, ← ha]
    exact (AdjoinRoot.lift_of _).symm
  refine ⟨ι.comp e.symm.toRingHom, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact hιinj.comp e.symm.injective
  · show ι (e.symm (qO p)) = T.qq n
    have : e.symm (qO p) = AdjoinRoot.root (fY p n) := by
      rw [RingEquiv.symm_apply_eq]
      show qO p = phiInv p n (AdjoinRoot.root _)
      rw [phiInv, AdjoinRoot.lift_root]
    rw [this]; exact AdjoinRoot.lift_root _
  · intro a b hb hb0
    have hbv : b = vL p n a := by
      ext r
      by_cases hr : (p : ℤ) ^ n ∣ r
      · obtain ⟨i, rfl⟩ := hr; rw [hb i, vL_coeff]
      · rw [hb0 r hr, vL_coeff_of_not_dvd p n a r hr]
    show ι (e.symm _) = _
    have : e.symm (algebraMap (Lau p) (O0 p) b) = AdjoinRoot.of _ (algebraMap (Lau p) (O0 p) a) := by
      rw [RingEquiv.symm_apply_eq, hbv, ← vO_alg]
      show _ = phiInv p n (AdjoinRoot.of _ _)
      rw [phiInv, AdjoinRoot.lift_of]
    rw [this]; exact AdjoinRoot.lift_of _
  · ext y
    simp only [RingHom.mem_range, Subalgebra.mem_toSubring, Algebra.adjoin_singleton_eq_range_aeval,
      AlgHom.mem_range]
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨g, hg⟩ := AdjoinRoot.mk_surjective (e.symm x)
      refine ⟨g, ?_⟩
      show _ = ι (e.symm x)
      rw [← hg, AdjoinRoot.lift_mk]; rfl
    · rintro ⟨g, rfl⟩
      refine ⟨e (AdjoinRoot.mk _ g), ?_⟩
      show ι (e.symm (e _)) = _
      rw [e.symm_apply_apply, AdjoinRoot.lift_mk]; rfl

end GlobalTheory.Glue
