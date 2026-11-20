import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW.SemilocalColumn

/- English proof (translation)
Establish `hcop : Pairwise (Function.onFun IsCoprime fun M : MaximalSpectrum A => M.asIdeal)`. Introduce `M N hMN`. Conclude with `Ideal.isCoprime_iff_sup_eq.mpr (M.isMaximal.coprime_of_ne N.isMaximal fun h => hMN (MaximalSpectrum.ext h))`. Take `⟨a, ha⟩` from `Ideal.pi_quotient_surjective hcop fun M => Ideal.Quotient.mk M.asIdeal (y M)`. Conclude with `⟨a, fun M => Ideal.Quotient.eq.mp (ha M)⟩`.
-/
private lemma exists_sub_iota_mem_of_sub_involution_mem (A : Type) [CommRing A] [Finite (MaximalSpectrum A)]
    (y : MaximalSpectrum A → A) : ∃ a : A, ∀ M : MaximalSpectrum A, a - y M ∈ M.asIdeal := by
  have hcop : Pairwise (Function.onFun IsCoprime fun M : MaximalSpectrum A => M.asIdeal) := by
    intro M N hMN
    exact Ideal.isCoprime_iff_sup_eq.mpr
      (M.isMaximal.coprime_of_ne N.isMaximal fun h => hMN (MaximalSpectrum.ext h))
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hcop fun M => Ideal.Quotient.mk M.asIdeal (y M)
  exact ⟨a, fun M => Ideal.Quotient.eq.mp (ha M)⟩

/- English proof (translation)
Establish `hnot : ∀ M : MaximalSpectrum A, x 0 ∈ M.asIdeal → ∃ k : Fin m, x k.succ ∉ M.asIdeal`. Introduce `M h0`. Assume the negation of the conclusion as `hall`. Simplify using `only [not_exists, not_not] at hall`. Take `⟨c, hc⟩` from `hx`.

Establish `hmem : ∀ i, x i ∈ M.asIdeal` using `fun i => Fin.cases h0 hall i`. Apply `M.isMaximal.ne_top` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hc]`. Conclude with `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hmem i)`. Use `choose kM hkM using hnot`.

Set `y : Fin m → MaximalSpectrum A → A` to `fun k M => if h : x 0 ∈ M.asIdeal then (if kM M h = k then 1 else 0) else 0`. Use `choose a ha using fun k => exists_sub_iota_mem_of_sub_involution_mem A (y k)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hu`. Take `⟨N, hN, hle⟩` from `Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.mpr hu)`.

Set `M : MaximalSpectrum A` to `⟨N, hN⟩`. Establish `huM : x 0 + ∑ k, a k * x k.succ ∈ M.asIdeal` using `hle (Ideal.mem_span_singleton_self _)`. Distinguish the cases in `h0 : x 0 ∈ M.asIdeal`. Establish `hy : ∑ k, y k M * x k.succ = x (kM M h0).succ`. Simplify using `only [y, dif_pos h0, ite_mul, one_mul, zero_mul]`.

Simplify using `[Finset.sum_ite_eq]`. Establish `hin : x 0 + ∑ k, (a k - y k M) * x k.succ ∈ M.asIdeal` using `M.asIdeal.add_mem h0 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (ha k M))`. Establish `e : x (kM M h0).succ = (x 0 + ∑ k, a k * x k.succ) - (x 0 + ∑ k, (a k - y k M) * x k.succ)`. Rewrite using `[← hy]`. Simplify using `only [sub_mul, Finset.sum_sub_distrib]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `hkM M h0 (e ▸ M.asIdeal.sub_mem huM hin)`. Apply `h0` to reduce the goal to its premises. Establish `hs : ∑ k, a k * x k.succ ∈ M.asIdeal`. Use `Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_` and prove the remaining obligations.

Simplify `ha k M` using `[y, h0]`. Simplify using `using M.asIdeal.sub_mem huM hs`.
-/
theorem exists_isUnit_add (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (m : ℕ)
    (x : Fin (m + 1) → A) (hx : ∃ c : Fin (m + 1) → A, ∑ i, c i * x i = 1) :
    ∃ a : Fin m → A, IsUnit (x 0 + ∑ k, a k * x k.succ) := by
  classical
  have hnot : ∀ M : MaximalSpectrum A, x 0 ∈ M.asIdeal → ∃ k : Fin m, x k.succ ∉ M.asIdeal := by
    intro M h0
    by_contra hall
    simp only [not_exists, not_not] at hall
    obtain ⟨c, hc⟩ := hx
    have hmem : ∀ i, x i ∈ M.asIdeal := fun i => Fin.cases h0 hall i
    apply M.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one, ← hc]
    exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (hmem i)
  choose kM hkM using hnot
  let y : Fin m → MaximalSpectrum A → A := fun k M =>
    if h : x 0 ∈ M.asIdeal then (if kM M h = k then 1 else 0) else 0
  choose a ha using fun k => exists_sub_iota_mem_of_sub_involution_mem A (y k)
  refine ⟨a, ?_⟩
  by_contra hu
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal _ (Ideal.span_singleton_eq_top.not.mpr hu)
  let M : MaximalSpectrum A := ⟨N, hN⟩
  have huM : x 0 + ∑ k, a k * x k.succ ∈ M.asIdeal := hle (Ideal.mem_span_singleton_self _)
  by_cases h0 : x 0 ∈ M.asIdeal
  · have hy : ∑ k, y k M * x k.succ = x (kM M h0).succ := by
      simp only [y, dif_pos h0, ite_mul, one_mul, zero_mul]
      simp [Finset.sum_ite_eq]
    have hin : x 0 + ∑ k, (a k - y k M) * x k.succ ∈ M.asIdeal :=
      M.asIdeal.add_mem h0 (Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (ha k M))
    have e : x (kM M h0).succ =
        (x 0 + ∑ k, a k * x k.succ) - (x 0 + ∑ k, (a k - y k M) * x k.succ) := by
      rw [← hy]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    exact hkM M h0 (e ▸ M.asIdeal.sub_mem huM hin)
  · apply h0
    have hs : ∑ k, a k * x k.succ ∈ M.asIdeal := by
      refine Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ ?_
      simpa [y, h0] using ha k M
    simpa using M.asIdeal.sub_mem huM hs

/- English proof (translation)
Introduce `A _ _ m x hx`. Take `⟨a, ha⟩` from `exists_isUnit_add A m x hx`. Use `set u := x 0 + ∑ k, a k * x k.succ with hu`. Set `b : Fin (m + 1) → A` to `Fin.cons 0 a`. Set `E : Matrix (Fin (m + 1)) (Fin (m + 1)) A` to `Matrix.of fun i j => if i = j then 1 else if i = 0 then -b j else 0`.

Set `D : Matrix (Fin (m + 1)) (Fin (m + 1)) A` to `Matrix.of fun i j => if j = 0 then (if i = 0 then u else x i) else if i = j then 1 else 0`. Establish `hE : E.det = 1`. Rewrite using `[Matrix.det_of_isUpperTriangular]`. Conclude with `Finset.prod_eq_one fun i _ => by simp [E]`. Introduce `i j hij`.

Establish `hji : j < i` using `hij`. Establish `hi : i ≠ 0`. Introduce and unpack `rfl`. Conclude with `Fin.not_lt_zero _ hji`. Simplify using `[E, hji.ne', hi]`.

Establish `hD : D.det = u`. Rewrite using `[Matrix.det_of_isLowerTriangular]`. Rewrite using `[Fin.prod_univ_succ]`. Simplify using `[D, Fin.succ_ne_zero]`. Introduce `i j hij`.

Establish `hij' : i < j` using `hij`. Establish `hj : j ≠ 0`. Introduce and unpack `rfl`. Conclude with `Fin.not_lt_zero _ hij'`. Simplify using `[D, hj, hij'.ne]`.

Use `⟨E * D, ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_mul, hE, hD, one_mul]`. Conclude with `ha`. Rewrite using `[Matrix.mul_apply]`. Distinguish the cases in `hi : i = 0`.

Substitute `hi` using the available equality. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `[E, D, b, (Fin.succ_ne_zero _).symm, hu, Finset.sum_neg_distrib]`. Rewrite using `[Finset.sum_eq_single i]`. Simplify using `[E, D, hi]`.

Introduce `j _ hji`. Simplify using `[E, D, Ne.symm hji, hi]`. Simplify using the standard rewrite rules.
-/
theorem exists_invertible_first_column :
    ∀ (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (m : ℕ) (x : Fin (m + 1) → A),
      (∃ c : Fin (m + 1) → A, ∑ i, c i * x i = 1) →
      ∃ g : Matrix (Fin (m + 1)) (Fin (m + 1)) A, IsUnit g.det ∧ ∀ i, g i 0 = x i := by
  intro A _ _ m x hx
  classical
  obtain ⟨a, ha⟩ := exists_isUnit_add A m x hx
  set u := x 0 + ∑ k, a k * x k.succ with hu
  let b : Fin (m + 1) → A := Fin.cons 0 a
  let E : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
    Matrix.of fun i j => if i = j then 1 else if i = 0 then -b j else 0
  let D : Matrix (Fin (m + 1)) (Fin (m + 1)) A :=
    Matrix.of fun i j => if j = 0 then (if i = 0 then u else x i) else if i = j then 1 else 0
  have hE : E.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular]
    · exact Finset.prod_eq_one fun i _ => by simp [E]
    · intro i j hij
      have hji : j < i := hij
      have hi : i ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hji
      simp [E, hji.ne', hi]
  have hD : D.det = u := by
    rw [Matrix.det_of_isLowerTriangular]
    · rw [Fin.prod_univ_succ]
      simp [D, Fin.succ_ne_zero]
    · intro i j hij
      have hij' : i < j := hij
      have hj : j ≠ 0 := by
        rintro rfl
        exact Fin.not_lt_zero _ hij'
      simp [D, hj, hij'.ne]
  refine ⟨E * D, ?_, fun i => ?_⟩
  · rw [Matrix.det_mul, hE, hD, one_mul]
    exact ha
  · rw [Matrix.mul_apply]
    by_cases hi : i = 0
    · subst hi
      rw [Fin.sum_univ_succ]
      simp [E, D, b, (Fin.succ_ne_zero _).symm, hu, Finset.sum_neg_distrib]
    · rw [Finset.sum_eq_single i]
      · simp [E, D, hi]
      · intro j _ hji
        simp [E, D, Ne.symm hji, hi]
      · simp

end GlobalTheory.CompanionTheory.SW.SemilocalColumn
