import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEventualPolyLine
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEventualValueFacts
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open Polynomial GroundTheory.Heights₂.Heights.NumbersDVR fwdDiff

noncomputable section

namespace EventualPolyLine

variable {K : Type}

def lineRestrict [Fintype K] (a c : K → ℚ) (p : MvPolynomial K ℚ) : ℚ[X] :=
  MvPolynomial.aeval (fun k => C (a k) * X + C (c k)) p

def topCoeff [Fintype K] (D : ℕ) (a : K → ℚ) (p : MvPolynomial K ℚ) : ℚ :=
  ∑ s ∈ p.support, p.coeff s * if ∑ k, s k = D then ∏ k, a k ^ s k else 0

/- English proof (translation)
Unfold `lineRestrict`. Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C r => simp`. Consider the case `add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]`. Consider the case `mul_X p k hp`.

Simplify using `only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eval_lineRestrict [Fintype K] (a c : K → ℚ) (p : MvPolynomial K ℚ) (t : ℚ) :
    (lineRestrict a c p).eval t = MvPolynomial.eval (fun k => c k + t * a k) p := by
  unfold lineRestrict
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p k hp =>
    simp only [map_mul, Polynomial.eval_mul, hp, MvPolynomial.aeval_X, MvPolynomial.eval_X,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_X]
    ring

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert k S hk ih`. Establish `h1 : ((C (a k) * X + C (c k)) ^ (s k)).natDegree ≤ s k`. Simplify using `using natDegree_pow_le_of_le (s k) (natDegree_linear_le (a := a k) (b := c k))`.

Establish `h2 : ((C (a k) * X + C (c k)) ^ (s k)).coeff (s k) = a k ^ s k`. Use `coeff_pow_of_natDegree_le (m := s k) (natDegree_linear_le (a := a k) (b := c k))` as an intermediate fact. Simplify using `using this`. Rewrite using `[Finset.prod_insert hk, Finset.sum_insert hk, Finset.prod_insert hk]`. Conclude with `⟨natDegree_mul_le.trans (add_le_add h1 ih.1), by rw [coeff_mul_add_eq_of_natDegree_le h1 ih.1, h2, ih.2]⟩`.
-/
theorem prod_line_pow (a c : K → ℚ) (s : K → ℕ) (S : Finset K) :
    (∏ k ∈ S, (C (a k) * X + C (c k)) ^ (s k)).natDegree ≤ ∑ k ∈ S, s k ∧
      (∏ k ∈ S, (C (a k) * X + C (c k)) ^ (s k)).coeff (∑ k ∈ S, s k) = ∏ k ∈ S, a k ^ (s k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
    have h1 : ((C (a k) * X + C (c k)) ^ (s k)).natDegree ≤ s k := by
      simpa using natDegree_pow_le_of_le (s k) (natDegree_linear_le (a := a k) (b := c k))
    have h2 : ((C (a k) * X + C (c k)) ^ (s k)).coeff (s k) = a k ^ s k := by
      have := coeff_pow_of_natDegree_le (m := s k) (natDegree_linear_le (a := a k) (b := c k))
      simpa using this
    rw [Finset.prod_insert hk, Finset.sum_insert hk, Finset.prod_insert hk]
    exact ⟨natDegree_mul_le.trans (add_le_add h1 ih.1),
      by rw [coeff_mul_add_eq_of_natDegree_le h1 ih.1, h2, ih.2]⟩

/- English proof (translation)
Establish `hs : ∀ s ∈ p.support, ∑ k, s k ≤ D` using `fun s hs => by`. Use `MvPolynomial.le_totalDegree hs` as an intermediate fact. Rewrite `this` using `[Finsupp.sum_fintype _ _ (fun _ => rfl)]`. Conclude with `this.trans hp`. Establish `hexp : lineRestrict a c p = ∑ s ∈ p.support, C (p.coeff s) * ∏ k, (C (a k) * X + C (c k)) ^ (s k)`.

Unfold `lineRestrict`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']`. Both sides reduce to the same expression. Rewrite using `[hexp]`. Prove the components needed by the constructor for the conclusion.

Use `natDegree_sum_le_of_forall_le _ _ (fun s hs' => ?_)` and prove the remaining obligations. Conclude with `(natDegree_C_mul_le _ _).trans ((prod_line_pow a c s Finset.univ).1.trans (hs s hs'))`. Rewrite using `[Polynomial.finsetSum_coeff]`. Use `Finset.sum_congr rfl (fun s hs' => ?_)` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_C_mul]`.

Use `congr 1`. Use `split_ifs with hD`. Rewrite using `[← hD]`. Conclude with `(prod_line_pow a c s Finset.univ).2`. Conclude with `coeff_eq_zero_of_natDegree_lt ((prod_line_pow a c s Finset.univ).1.trans_lt (lt_of_le_of_ne (hs s hs') hD))`.
-/
theorem lineRestrict_natDegree_coeff [Fintype K] (D : ℕ) (a c : K → ℚ) (p : MvPolynomial K ℚ)
    (hp : p.totalDegree ≤ D) :
    (lineRestrict a c p).natDegree ≤ D ∧ (lineRestrict a c p).coeff D = topCoeff D a p := by
  have hs : ∀ s ∈ p.support, ∑ k, s k ≤ D := fun s hs => by
    have := MvPolynomial.le_totalDegree hs
    rw [Finsupp.sum_fintype _ _ (fun _ => rfl)] at this
    exact this.trans hp
  have hexp : lineRestrict a c p =
      ∑ s ∈ p.support, C (p.coeff s) * ∏ k, (C (a k) * X + C (c k)) ^ (s k) := by
    unfold lineRestrict
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
    rfl
  rw [hexp]
  constructor
  · refine natDegree_sum_le_of_forall_le _ _ (fun s hs' => ?_)
    exact (natDegree_C_mul_le _ _).trans ((prod_line_pow a c s Finset.univ).1.trans (hs s hs'))
  · rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl (fun s hs' => ?_)
    rw [Polynomial.coeff_C_mul]
    congr 1
    split_ifs with hD
    · rw [← hD]
      exact (prod_line_pow a c s Finset.univ).2
    · exact coeff_eq_zero_of_natDegree_lt
        ((prod_line_pow a c s Finset.univ).1.trans_lt (lt_of_le_of_ne (hs s hs') hD))

/- English proof (translation)
Break down `hP.lt_or_eq with h | h` into its components or cases. Rewrite using `[Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, coeff_eq_zero_of_natDegree_lt h]`. Simplify using the standard rewrite rules. Substitute `h` using the available equality. Rewrite using `[Polynomial.fwdDiff_iter_degree_eq_factorial]`.

Rewrite using `[Polynomial.coeff_natDegree]`. Simplify using `only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fwdDiff_iter_poly (D : ℕ) (P : ℚ[X]) (hP : P.natDegree ≤ D) :
    (fwdDiff (1 : ℚ))^[D] P.eval 0 = (D.factorial : ℚ) * P.coeff D := by
  rcases hP.lt_or_eq with h | h
  · rw [Polynomial.fwdDiff_iter_eq_zero_of_degree_lt h, coeff_eq_zero_of_natDegree_lt h]
    simp
  · subst h
    rw [Polynomial.fwdDiff_iter_degree_eq_factorial]
    rw [Polynomial.coeff_natDegree]
    simp only [Pi.smul_apply, Pi.natCast_apply, smul_eq_mul]
    ring

/- English proof (translation)
Simplify using `only [mixedDiff, List.ofFn_const]`.
-/
theorem mixedDiff_const (D : ℕ) (a : K → ℤ) (f : (K → ℤ) → ℤ) :
    mixedDiff (fun _ : Fin D => a) f = (List.replicate D a).foldr diffStep f := by
  simp only [mixedDiff, List.ofFn_const]

/- English proof (translation)
Proceed by induction on `n generalizing x with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `e1 : x - (n + 1) • a + a = x - n • a` using `by rw [succ_nsmul]; abel`. Establish `e2 : x - a - n • a = x - (n + 1) • a` using `by rw [succ_nsmul]; abel`.

Rewrite using `[List.replicate_succ, List.foldr_cons, Function.iterate_succ_apply']`. Use `show (List.replicate n a).foldr diffStep f x - (List.replicate n a).foldr diffStep f (x - a) = _`. Rewrite using `[ih, ih, e2]`. Use `show _ = (fwdDiff a)^[n] f (x - (n + 1) • a + a) - (fwdDiff a)^[n] f (x - (n + 1) • a)`. Rewrite using `[e1]`.
-/
theorem foldr_diffStep_replicate (a : K → ℤ) (f : (K → ℤ) → ℤ) (n : ℕ) (x : K → ℤ) :
    (List.replicate n a).foldr diffStep f x = (fwdDiff a)^[n] f (x - n • a) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have e1 : x - (n + 1) • a + a = x - n • a := by rw [succ_nsmul]; abel
    have e2 : x - a - n • a = x - (n + 1) • a := by rw [succ_nsmul]; abel
    rw [List.replicate_succ, List.foldr_cons, Function.iterate_succ_apply']
    show (List.replicate n a).foldr diffStep f x - (List.replicate n a).foldr diffStep f (x - a) = _
    rw [ih, ih, e2]
    show _ = (fwdDiff a)^[n] f (x - (n + 1) • a + a) - (fwdDiff a)^[n] f (x - (n + 1) • a)
    rw [e1]

end EventualPolyLine

open EventualPolyLine in

/- English proof (translation)
Introduce `K _ _ D f p a₀ a m hp hf`. Take `⟨aQ, haQ⟩ : ∃ aQ : K → ℚ, aQ = fun k => (a k : ℚ)` from `⟨_, rfl⟩`. Establish `key : ∀ x : K → ℤ, (∀ k, (a₀ : ℤ) + D * |a k| ≤ x k) → ((mixedDiff (fun _ : Fin D => a) f x : ℤ) : ℚ) = (D.factorial : ℚ) * topCoeff D aQ p`. Introduce `x hx`. Take `⟨c, hc⟩ : ∃ c : K → ℚ, c = fun k => (((x - D • a) k : ℤ) : ℚ)` from `⟨_, rfl⟩`.

Take `⟨hdeg, hcoeff⟩` from `lineRestrict_natDegree_coeff D aQ c p hp`. Rewrite using `[mixedDiff_const, foldr_diffStep_replicate, fwdDiff_iter_eq_sum_shift, ← hcoeff, ← fwdDiff_iter_poly D _ hdeg, fwdDiff_iter_eq_sum_shift, Int.cast_sum]`. Use `Finset.sum_congr rfl (fun j hj => ?_)` and prove the remaining obligations. Establish `hjD : j ≤ D` using `Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)`. Establish `hnn : ∀ k, (a₀ : ℤ) ≤ (x - D • a + j • a) k`.

Introduce `k`. Establish `h1` using `hx k`. Establish `hj' : (j : ℤ) ≤ D` using `by exact_mod_cast hjD`. Establish `hj0 : (0 : ℤ) ≤ j` using `by positivity`. Simplify using `only [Pi.add_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]`.

Apply the tactic sequence `rcases abs_cases (a k) with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> nlinarith`. Establish `hge : ∀ k, a₀ ≤ ((x - D • a + j • a) k).toNat` using `fun k => by have := hnn k; omega`. Establish `hy : (fun k => ((((x - D • a + j • a) k).toNat : ℕ) : ℤ)) = x - D • a + j • a`. Use function extensionality and compare the values at `fun k => Int.toNat_of_nonneg (by have := hnn k; omega)`. Establish `hfy : f (x - D • a + j • a) = f (fun k => ((((x - D • a + j • a) k).toNat : ℕ) : ℤ))`.

Rewrite using `[hy]`. Rewrite using `[smul_eq_mul, zsmul_eq_mul, Int.cast_mul, hfy, hf _ hge, eval_lineRestrict]`. Use `congr 2`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Establish `e2 : ((((x - D • a + j • a) k).toNat : ℕ) : ℚ) = (((x - D • a + j • a) k : ℤ) : ℚ)`. Rewrite using `[← Int.cast_natCast, Int.toNat_of_nonneg (by have := hnn k; omega)]`. Rewrite using `[e2, hc, haQ]`. Simplify using `only [Pi.add_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, zero_add, mul_one]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨c₀, hc₀⟩ : ∃ c₀, mixedDiff (fun _ : Fin D => a) f (fun k => (a₀ : ℤ) + D * |a k|) = c₀` from `⟨_, rfl⟩`. Establish `h₀` using `key (fun k => (a₀ : ℤ) + D * |a k|) (fun k => le_rfl)`. Rewrite `h₀` using `[hc₀]`. Establish `hev : ∀ᶠ x in Filter.atTop, mixedDiff (fun _ : Fin D => a) f x = c₀`.

Use `Filter.eventually_atTop.2 ⟨fun k => (a₀ : ℤ) + D * |a k|, fun x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `key x (fun k => hx k)`. Conclude with `h1.trans h₀.symm` after adjusting the coercions. Establish `hEV` using `(EventualValueFacts.proof K _ c₀ 0).1 hev`. Take `⟨hdeg, hcoeff⟩` from `lineRestrict_natDegree_coeff D aQ (fun k => (m k : ℚ)) p hp`.

Use `⟨(lineRestrict aQ (fun k => (m k : ℚ)) p).map (algebraMap ℚ ℝ), natDegree_map_le.trans hdeg, ?_, ?_⟩` and prove the remaining obligations. Establish `hD : (D.factorial : ℝ) ≠ 0` using `by positivity`. Rewrite using `[Polynomial.coeff_map, hcoeff, hEV, eq_ratCast, eq_div_iff hD, show ((c₀ : ℤ) : ℝ) = (((c₀ : ℤ) : ℚ) : ℝ) by norm_cast, h₀]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Introduce `n`. Rewrite using `[Polynomial.eval_natCast_map, eval_lineRestrict, eq_ratCast]`. Use `congr 2`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Rewrite using `[haQ]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem EventualPolyLine.proof : EventualPolyLine.Statement := by
  intro K _ _ D f p a₀ a m hp hf
  obtain ⟨aQ, haQ⟩ : ∃ aQ : K → ℚ, aQ = fun k => (a k : ℚ) := ⟨_, rfl⟩
  have key : ∀ x : K → ℤ, (∀ k, (a₀ : ℤ) + D * |a k| ≤ x k) →
      ((mixedDiff (fun _ : Fin D => a) f x : ℤ) : ℚ) = (D.factorial : ℚ) * topCoeff D aQ p := by
    intro x hx
    obtain ⟨c, hc⟩ : ∃ c : K → ℚ, c = fun k => (((x - D • a) k : ℤ) : ℚ) := ⟨_, rfl⟩
    obtain ⟨hdeg, hcoeff⟩ := lineRestrict_natDegree_coeff D aQ c p hp
    rw [mixedDiff_const, foldr_diffStep_replicate, fwdDiff_iter_eq_sum_shift, ← hcoeff,
      ← fwdDiff_iter_poly D _ hdeg, fwdDiff_iter_eq_sum_shift, Int.cast_sum]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hnn : ∀ k, (a₀ : ℤ) ≤ (x - D • a + j • a) k := by
      intro k
      have h1 := hx k
      have hj' : (j : ℤ) ≤ D := by exact_mod_cast hjD
      have hj0 : (0 : ℤ) ≤ j := by positivity
      simp only [Pi.add_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
      rcases abs_cases (a k) with ⟨h2, h3⟩ | ⟨h2, h3⟩ <;> nlinarith
    have hge : ∀ k, a₀ ≤ ((x - D • a + j • a) k).toNat := fun k => by have := hnn k; omega
    have hy : (fun k => ((((x - D • a + j • a) k).toNat : ℕ) : ℤ)) = x - D • a + j • a :=
      funext fun k => Int.toNat_of_nonneg (by have := hnn k; omega)
    have hfy : f (x - D • a + j • a) = f (fun k => ((((x - D • a + j • a) k).toNat : ℕ) : ℤ)) := by
      rw [hy]
    rw [smul_eq_mul, zsmul_eq_mul, Int.cast_mul, hfy, hf _ hge, eval_lineRestrict]
    congr 2
    congr 1
    funext k
    have e2 : ((((x - D • a + j • a) k).toNat : ℕ) : ℚ) = (((x - D • a + j • a) k : ℤ) : ℚ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg (by have := hnn k; omega)]
    rw [e2, hc, haQ]
    simp only [Pi.add_apply, Pi.sub_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, zero_add, mul_one]
    push_cast
    ring
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, mixedDiff (fun _ : Fin D => a) f (fun k => (a₀ : ℤ) + D * |a k|) = c₀ :=
    ⟨_, rfl⟩
  have h₀ := key (fun k => (a₀ : ℤ) + D * |a k|) (fun k => le_rfl)
  rw [hc₀] at h₀
  have hev : ∀ᶠ x in Filter.atTop, mixedDiff (fun _ : Fin D => a) f x = c₀ := by
    refine Filter.eventually_atTop.2 ⟨fun k => (a₀ : ℤ) + D * |a k|, fun x hx => ?_⟩
    have h1 := key x (fun k => hx k)
    exact_mod_cast h1.trans h₀.symm
  have hEV := (EventualValueFacts.proof K _ c₀ 0).1 hev
  obtain ⟨hdeg, hcoeff⟩ := lineRestrict_natDegree_coeff D aQ (fun k => (m k : ℚ)) p hp
  refine ⟨(lineRestrict aQ (fun k => (m k : ℚ)) p).map (algebraMap ℚ ℝ), natDegree_map_le.trans hdeg, ?_, ?_⟩
  · have hD : (D.factorial : ℝ) ≠ 0 := by positivity
    rw [Polynomial.coeff_map, hcoeff, hEV, eq_ratCast, eq_div_iff hD,
      show ((c₀ : ℤ) : ℝ) = (((c₀ : ℤ) : ℚ) : ℝ) by norm_cast, h₀]
    push_cast
    ring
  · intro n
    rw [Polynomial.eval_natCast_map, eval_lineRestrict, eq_ratCast]
    congr 2
    congr 1
    funext k
    rw [haQ]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
