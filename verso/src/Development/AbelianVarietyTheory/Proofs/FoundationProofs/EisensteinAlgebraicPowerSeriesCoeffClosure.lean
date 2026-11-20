import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.AlgPowerSeries

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, rfl⟩ k`. Rewrite using `[PowerSeries.coeff_map]`. Conclude with `(PowerSeries.coeff k g).2`. Introduce `h`.

Use `⟨PowerSeries.mk fun k => ⟨PowerSeries.coeff k f, h k⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `k`. Simplify using `[PowerSeries.coeff_map]`.
-/
theorem mem_range_map_iff {L : Type} [CommRing L] (B : Subring L) (f : PowerSeries L) :
    f ∈ (PowerSeries.map B.subtype).range ↔ ∀ k, PowerSeries.coeff k f ∈ B := by
  constructor
  · rintro ⟨g, rfl⟩ k
    rw [PowerSeries.coeff_map]; exact (PowerSeries.coeff k g).2
  · intro h
    refine ⟨PowerSeries.mk fun k => ⟨PowerSeries.coeff k f, h k⟩, ?_⟩
    ext k; simp [PowerSeries.coeff_map]

/- English proof (translation)
Introduce `L _ _ A b Q hQ hA hb`. Take `⟨RA, hRAdef⟩ : ∃ RA : Subring (PowerSeries L), RA = (PowerSeries.map A.subtype).range` from `⟨_, rfl⟩`. Establish `hex : ∃ d, ∃ R : Polynomial (PowerSeries L), R ≠ 0 ∧ (∀ i, R.coeff i ∈ RA) ∧ R.eval b = 0 ∧ R.natDegree = d` using `⟨Q.natDegree, Q, hQ, fun i => hRAdef ▸ (mem_range_map_iff A _).2 (hA i), hb, rfl⟩`. Take `⟨R, hR0, hRA', hRb, hRd⟩` from `Nat.find_spec hex`. Establish `hmin : ∀ R' : Polynomial (PowerSeries L), R' ≠ 0 → (∀ i, R'.coeff i ∈ RA) → R'.natDegree < R.natDegree → R'.eval b ≠ 0`.

Introduce `R' h0 hc hlt he`. Conclude with `Nat.find_min hex (by omega) ⟨R', h0, hc, he, rfl⟩`. Establish `hdeg : R.natDegree ≠ 0`. Introduce `h`. Rewrite `hRb` using `[Polynomial.eq_C_of_natDegree_eq_zero h, Polynomial.eval_C]`.

Apply `hR0` to reduce the goal to its premises. Rewrite using `[Polynomial.eq_C_of_natDegree_eq_zero h, hRb, map_zero]`. Take `⟨D, hD⟩ : ∃ D, D = Polynomial.derivative R` from `⟨_, rfl⟩`. Establish `hD0 : D ≠ 0` using `by haveI : IsAddTorsionFree (PowerSeries L) := IsAddTorsionFree.of_isTorsionFree L _`. Introduce `h`.

Rewrite `h` using `[hD]`. Conclude with `hdeg (Polynomial.natDegree_eq_zero_of_derivative_eq_zero h)`. Establish `hDc : ∀ i, D.coeff i ∈ RA`. Introduce `i`. Rewrite using `[hD, Polynomial.coeff_derivative]`.

Conclude with `RA.mul_mem (hRA' _) (RA.add_mem (natCast_mem RA _) RA.one_mem)`. Establish `hDb : D.eval b ≠ 0` using `hmin D hD0 hDc (hD ▸ Polynomial.natDegree_derivative_lt hdeg)`. Take `⟨F, hF⟩ : ∃ F, F = D.eval b` from `⟨_, rfl⟩`. Establish `hex2 : ∃ m, PowerSeries.coeff m F ≠ 0`. Assume the negation of the conclusion as `h; push_neg at h; exact hDb (hF ▸ PowerSeries.ext fun k => by simpa using h k)`.

Take `⟨m, hc, hlow⟩ : ∃ m, PowerSeries.coeff m F ≠ 0 ∧ ∀ i < m, PowerSeries.coeff i F = 0` from `⟨Nat.find hex2, Nat.find_spec hex2, fun i hi => not_not.mp (Nat.find_min hex2 hi)⟩`. Take `⟨c, hcdef⟩ : ∃ c, c = PowerSeries.coeff m F` from `⟨_, rfl⟩`. Rewrite `hc` using `[← hcdef]`. Use `⟨insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b), ?_⟩` and prove the remaining obligations. Take `⟨B, hBdef⟩ : ∃ B, B = Subring.closure ((A : Set L) ∪ ↑(insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b)))` from `⟨_, rfl⟩`.

Rewrite using `[← hBdef]`. Establish `hAB : ∀ x ∈ A, x ∈ B` using `fun x hx => hBdef ▸ Subring.subset_closure (Or.inl hx)`. Establish `hcB : c⁻¹ ∈ B` using `hBdef ▸ Subring.subset_closure (Or.inr (by simp))`. Establish `hbB : ∀ i ≤ m, PowerSeries.coeff i b ∈ B` using `fun i hi => hBdef ▸ Subring.subset_closure (Or.inr (by simp; exact Or.inr ⟨i, by omega, rfl⟩))`. Take `⟨RB, hRBdef⟩ : ∃ RB : Subring (PowerSeries L), RB = (PowerSeries.map B.subtype).range` from `⟨_, rfl⟩`.

Establish `hRARB : ∀ f ∈ RA, f ∈ RB` using `fun f hf => by`. Rewrite using `[hRBdef]`. Rewrite `hf` using `[hRAdef]`. Conclude with `(mem_range_map_iff B f).2 fun k => hAB _ ((mem_range_map_iff A f).1 hf k)`. Introduce `n`.

Use `Nat.strong_induction_on n ?_` and prove the remaining obligations. Introduce `n ih`. Break down `le_or_gt n m with hnm | hmn` into its components or cases. Conclude with `hbB n hnm`. Take `⟨u, hu⟩ : ∃ u : PowerSeries L, u = PowerSeries.mk fun k => if k < n then PowerSeries.coeff k b else 0` from `⟨_, rfl⟩`.

Take `⟨v, hv⟩ : ∃ v : PowerSeries L, v = PowerSeries.mk fun k => PowerSeries.coeff (n + k) b` from `⟨_, rfl⟩`. Establish `hbuv : b = u + PowerSeries.X ^ n * v`. Use extensionality with `k`. Rewrite using `[map_add, PowerSeries.coeff_X_pow_mul', hu, hv]`. Simplify using `only [PowerSeries.coeff_mk]`.

Distinguish the cases in `h1 : k < n`. Rewrite using `[if_pos h1, if_neg (by omega), add_zero]`. Rewrite using `[if_neg h1, if_pos (by omega), zero_add, show n + (k - n) = k by omega]`. Establish `huB : u ∈ RB`. Rewrite using `[hRBdef]`.

Use `(mem_range_map_iff B u).2 fun k => ?_` and prove the remaining obligations. Rewrite using `[hu, PowerSeries.coeff_mk]`. Use `split_ifs with h`. Conclude with `ih k h`. Conclude with `B.zero_mem`.

Establish `hRu : R.eval u ∈ RB`. Rewrite using `[Polynomial.eval_eq_sum_range]`. Conclude with `RB.sum_mem fun i _ => RB.mul_mem (hRARB _ (hRA' i)) (RB.pow_mem huB _)`. Establish `hdvd : PowerSeries.X ^ n ∣ F - D.eval u`. Establish `h1` using `Polynomial.sub_dvd_eval_sub b u D`.

Establish `h2 : b - u = PowerSeries.X ^ n * v` using `by rw [hbuv]; ring`. Rewrite `h1` using `[h2, ← hF]`. Conclude with `(dvd_mul_right _ _).trans h1`. Take `⟨w, hw⟩` from `hdvd`. Take `⟨k, hk⟩` from `R.binomExpansion u (PowerSeries.X ^ n * v)`.

Rewrite `hk` using `[← hbuv, hRb, ← hD]`. Establish `hDu : D.eval u = F - PowerSeries.X ^ n * w` using `by rw [← hw]; ring`. Rewrite `hk` using `[hDu]`. Establish `key : 0 = R.eval u + PowerSeries.X ^ n * (F * v) + PowerSeries.X ^ (n + n) * (k * v ^ 2 - w * v)`. Rewrite using `[hk]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hc2` using `congrArg (PowerSeries.coeff (n + m)) key`. Rewrite `hc2` using `[map_zero, map_add, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul', if_pos (by omega), if_neg (by omega), add_zero, Nat.add_sub_cancel_left]`. Establish `hFv : PowerSeries.coeff m (F * v) = c * PowerSeries.coeff n b`. Rewrite using `[PowerSeries.coeff_mul, Finset.sum_eq_single (m, 0)]`.

Rewrite using `[← hcdef, hv, PowerSeries.coeff_mk, add_zero]`. Introduce and unpack `⟨i, j⟩ hij hne`. Establish `hij' : i + j = m` using `by simpa using hij`. Establish `him : i < m`. Break down `Nat.lt_or_ge i m with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Apply `hne` to reduce the goal to its premises. Simplify using `only [Prod.mk.injEq]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hlow i him, zero_mul]`. Introduce `h; exfalso; exact h (by simp)`. Establish `hcn : c * PowerSeries.coeff n b ∈ B`. Establish `e : c * PowerSeries.coeff n b = - PowerSeries.coeff (n + m) (R.eval u)`. Take the linear combination `-hc2 - hFv`.

Rewrite using `[e]`. Rewrite `hRu` using `[hRBdef]`. Conclude with `B.neg_mem ((mem_range_map_iff B _).1 hRu _)`. Establish `e2 : PowerSeries.coeff n b = c⁻¹ * (c * PowerSeries.coeff n b)`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hc, one_mul]`.

Rewrite using `[e2]`. Conclude with `B.mul_mem hcB hcn`.
-/
theorem exists_finset_coeff_mem_closure :
    ∀ (L : Type) [Field L] [CharZero L] (A : Subring L) (b : PowerSeries L)
      (Q : Polynomial (PowerSeries L)), Q ≠ 0 →
      (∀ i k, PowerSeries.coeff k (Q.coeff i) ∈ A) → Q.eval b = 0 →
      ∃ S : Finset L, ∀ k, PowerSeries.coeff k b ∈ Subring.closure ((A : Set L) ∪ S) := by
  classical
  intro L _ _ A b Q hQ hA hb
  obtain ⟨RA, hRAdef⟩ : ∃ RA : Subring (PowerSeries L), RA = (PowerSeries.map A.subtype).range :=
    ⟨_, rfl⟩
  have hex : ∃ d, ∃ R : Polynomial (PowerSeries L), R ≠ 0 ∧ (∀ i, R.coeff i ∈ RA) ∧
      R.eval b = 0 ∧ R.natDegree = d :=
    ⟨Q.natDegree, Q, hQ, fun i => hRAdef ▸ (mem_range_map_iff A _).2 (hA i), hb, rfl⟩
  obtain ⟨R, hR0, hRA', hRb, hRd⟩ := Nat.find_spec hex
  have hmin : ∀ R' : Polynomial (PowerSeries L), R' ≠ 0 → (∀ i, R'.coeff i ∈ RA) →
      R'.natDegree < R.natDegree → R'.eval b ≠ 0 := by
    intro R' h0 hc hlt he
    exact Nat.find_min hex (by omega) ⟨R', h0, hc, he, rfl⟩
  have hdeg : R.natDegree ≠ 0 := by
    intro h
    rw [Polynomial.eq_C_of_natDegree_eq_zero h, Polynomial.eval_C] at hRb
    apply hR0; rw [Polynomial.eq_C_of_natDegree_eq_zero h, hRb, map_zero]
  obtain ⟨D, hD⟩ : ∃ D, D = Polynomial.derivative R := ⟨_, rfl⟩
  have hD0 : D ≠ 0 := by
    haveI : IsAddTorsionFree (PowerSeries L) := IsAddTorsionFree.of_isTorsionFree L _
    intro h; rw [hD] at h; exact hdeg (Polynomial.natDegree_eq_zero_of_derivative_eq_zero h)
  have hDc : ∀ i, D.coeff i ∈ RA := by
    intro i; rw [hD, Polynomial.coeff_derivative]
    exact RA.mul_mem (hRA' _) (RA.add_mem (natCast_mem RA _) RA.one_mem)
  have hDb : D.eval b ≠ 0 :=
    hmin D hD0 hDc (hD ▸ Polynomial.natDegree_derivative_lt hdeg)
  obtain ⟨F, hF⟩ : ∃ F, F = D.eval b := ⟨_, rfl⟩
  have hex2 : ∃ m, PowerSeries.coeff m F ≠ 0 := by
    by_contra h; push_neg at h; exact hDb (hF ▸ PowerSeries.ext fun k => by simpa using h k)
  obtain ⟨m, hc, hlow⟩ : ∃ m, PowerSeries.coeff m F ≠ 0 ∧ ∀ i < m, PowerSeries.coeff i F = 0 :=
    ⟨Nat.find hex2, Nat.find_spec hex2, fun i hi => not_not.mp (Nat.find_min hex2 hi)⟩
  obtain ⟨c, hcdef⟩ : ∃ c, c = PowerSeries.coeff m F := ⟨_, rfl⟩
  rw [← hcdef] at hc
  refine ⟨insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b), ?_⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = Subring.closure ((A : Set L) ∪
      ↑(insert c⁻¹ ((Finset.range (m+1)).image fun i => PowerSeries.coeff i b))) := ⟨_, rfl⟩
  rw [← hBdef]
  have hAB : ∀ x ∈ A, x ∈ B := fun x hx => hBdef ▸ Subring.subset_closure (Or.inl hx)
  have hcB : c⁻¹ ∈ B := hBdef ▸ Subring.subset_closure (Or.inr (by simp))
  have hbB : ∀ i ≤ m, PowerSeries.coeff i b ∈ B := fun i hi =>
    hBdef ▸ Subring.subset_closure (Or.inr (by simp; exact Or.inr ⟨i, by omega, rfl⟩))
  obtain ⟨RB, hRBdef⟩ : ∃ RB : Subring (PowerSeries L), RB = (PowerSeries.map B.subtype).range :=
    ⟨_, rfl⟩
  have hRARB : ∀ f ∈ RA, f ∈ RB := fun f hf => by
    rw [hRBdef]; rw [hRAdef] at hf
    exact (mem_range_map_iff B f).2 fun k => hAB _ ((mem_range_map_iff A f).1 hf k)
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases le_or_gt n m with hnm | hmn
  · exact hbB n hnm
  obtain ⟨u, hu⟩ : ∃ u : PowerSeries L,
      u = PowerSeries.mk fun k => if k < n then PowerSeries.coeff k b else 0 := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v : PowerSeries L,
      v = PowerSeries.mk fun k => PowerSeries.coeff (n + k) b := ⟨_, rfl⟩
  have hbuv : b = u + PowerSeries.X ^ n * v := by
    ext k
    rw [map_add, PowerSeries.coeff_X_pow_mul', hu, hv]
    simp only [PowerSeries.coeff_mk]
    by_cases h1 : k < n
    · rw [if_pos h1, if_neg (by omega), add_zero]
    · rw [if_neg h1, if_pos (by omega), zero_add, show n + (k - n) = k by omega]
  have huB : u ∈ RB := by
    rw [hRBdef]
    refine (mem_range_map_iff B u).2 fun k => ?_
    rw [hu, PowerSeries.coeff_mk]; split_ifs with h
    · exact ih k h
    · exact B.zero_mem
  have hRu : R.eval u ∈ RB := by
    rw [Polynomial.eval_eq_sum_range]
    exact RB.sum_mem fun i _ => RB.mul_mem (hRARB _ (hRA' i)) (RB.pow_mem huB _)
  have hdvd : PowerSeries.X ^ n ∣ F - D.eval u := by
    have h1 := Polynomial.sub_dvd_eval_sub b u D
    have h2 : b - u = PowerSeries.X ^ n * v := by rw [hbuv]; ring
    rw [h2, ← hF] at h1
    exact (dvd_mul_right _ _).trans h1
  obtain ⟨w, hw⟩ := hdvd
  obtain ⟨k, hk⟩ := R.binomExpansion u (PowerSeries.X ^ n * v)
  rw [← hbuv, hRb, ← hD] at hk
  have hDu : D.eval u = F - PowerSeries.X ^ n * w := by rw [← hw]; ring
  rw [hDu] at hk
  have key : 0 = R.eval u + PowerSeries.X ^ n * (F * v) +
      PowerSeries.X ^ (n + n) * (k * v ^ 2 - w * v) := by
    rw [hk]; ring
  have hc2 := congrArg (PowerSeries.coeff (n + m)) key
  rw [map_zero, map_add, map_add, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul',
    if_pos (by omega), if_neg (by omega), add_zero, Nat.add_sub_cancel_left] at hc2
  have hFv : PowerSeries.coeff m (F * v) = c * PowerSeries.coeff n b := by
    rw [PowerSeries.coeff_mul, Finset.sum_eq_single (m, 0)]
    · rw [← hcdef, hv, PowerSeries.coeff_mk, add_zero]
    · rintro ⟨i, j⟩ hij hne
      have hij' : i + j = m := by simpa using hij
      have him : i < m := by
        rcases Nat.lt_or_ge i m with h | h
        · exact h
        · exfalso; apply hne; simp only [Prod.mk.injEq]; omega
      rw [hlow i him, zero_mul]
    · intro h; exfalso; exact h (by simp)
  have hcn : c * PowerSeries.coeff n b ∈ B := by
    have e : c * PowerSeries.coeff n b = - PowerSeries.coeff (n + m) (R.eval u) := by
      linear_combination -hc2 - hFv
    rw [e]
    rw [hRBdef] at hRu
    exact B.neg_mem ((mem_range_map_iff B _).1 hRu _)
  have e2 : PowerSeries.coeff n b = c⁻¹ * (c * PowerSeries.coeff n b) := by
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  rw [e2]; exact B.mul_mem hcB hcn

end GlobalTheory.AlgPowerSeries
