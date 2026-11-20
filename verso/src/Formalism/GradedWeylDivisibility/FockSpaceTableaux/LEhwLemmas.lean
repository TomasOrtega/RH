import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.DualWeylDominanceOf

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Introduce `m hm k`. Set `N : ℕ` to `∏ d ∈ f.support, (coeff d f).den`. Set `u : MvPolynomial (Fin r × Fin n) ℤ` to `∑ d ∈ f.support, monomial d ((∏ d' ∈ f.support.erase d, ((coeff d' f).den : ℤ)) * (coeff d f).num)`. Establish `hu : map (Int.castRingHom ℚ) u = (N : ℚ) • f` using `by conv_rhs => rw [f.as_sum]`. Rewrite using `[Finset.smul_sum]`.

Simplify using `only [u, map_sum, map_monomial, smul_monomial]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Use `congr 1`. Use `push_cast`. Establish `hN : (N : ℚ) = (∏ d' ∈ f.support.erase d, ((coeff d' f).den : ℚ)) * (coeff d f).den`.

Simplify using `only [N]`. Use `push_cast`. Rewrite using `[Finset.prod_erase_mul _ _ hd]`. Rewrite using `[smul_eq_mul, hN, mul_assoc, Rat.den_mul_eq_num]`. Simplify using `[eq_intCast]`.

Establish `hN0 : (N : ℚ) ≠ 0`. Simplify using `only [N]`. Use `push_cast`. Conclude with `Finset.prod_ne_zero_iff.mpr fun d _ => Nat.cast_ne_zero.mpr (coeff d f).den_nz`. Establish `huD : u ∈ dualWeyl ℤ r n ν` using `(dualWeylIntRat r n ν u).mpr (by rw [hu]; exact (dualWeyl ℚ r n ν).smul_mem _ hf)`.

Establish `hmu : m ∈ u.support`. Rewrite using `[mem_support_iff]`. Introduce `h0`. Establish `e` using `congrArg (coeff m) hu`. Rewrite `e` using `[coeff_map, h0, map_zero, coeff_smul, smul_eq_mul]`.

Conclude with `(mem_support_iff.mp hm) ((mul_eq_zero.mp e.symm).resolve_left hN0)`. Conclude with `(dualWeylDominanceZ r n ν hnr hν u huD m hmu).1 k`.
-/
theorem lehw_dom {r n : ℕ} (ν : Fin n → ℕ) (hnr : n ≤ r) (hν : Antitone ν)
    (f : MvPolynomial (Fin r × Fin n) ℚ) (hf : f ∈ dualWeyl ℚ r n ν) :
    ∀ m ∈ f.support, ∀ k : ℕ,
      (∑ a : Fin r with a.val < k, rowDeg m a) ≤ ∑ a : Fin r with a.val < k, rowNu (r := r) ν a := by
  classical
  intro m hm k
  let N : ℕ := ∏ d ∈ f.support, (coeff d f).den
  let u : MvPolynomial (Fin r × Fin n) ℤ := ∑ d ∈ f.support,
    monomial d ((∏ d' ∈ f.support.erase d, ((coeff d' f).den : ℤ)) * (coeff d f).num)
  have hu : map (Int.castRingHom ℚ) u = (N : ℚ) • f := by
    conv_rhs => rw [f.as_sum]
    rw [Finset.smul_sum]
    simp only [u, map_sum, map_monomial, smul_monomial]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    push_cast
    have hN : (N : ℚ) = (∏ d' ∈ f.support.erase d, ((coeff d' f).den : ℚ)) * (coeff d f).den := by
      simp only [N]
      push_cast
      rw [Finset.prod_erase_mul _ _ hd]
    rw [smul_eq_mul, hN, mul_assoc, Rat.den_mul_eq_num]
    simp [eq_intCast]
  have hN0 : (N : ℚ) ≠ 0 := by
    simp only [N]
    push_cast
    exact Finset.prod_ne_zero_iff.mpr fun d _ => Nat.cast_ne_zero.mpr (coeff d f).den_nz
  have huD : u ∈ dualWeyl ℤ r n ν :=
    (dualWeylIntRat r n ν u).mpr (by rw [hu]; exact (dualWeyl ℚ r n ν).smul_mem _ hf)
  have hmu : m ∈ u.support := by
    rw [mem_support_iff]
    intro h0
    have e := congrArg (coeff m) hu
    rw [coeff_map, h0, map_zero, coeff_smul, smul_eq_mul] at e
    exact (mem_support_iff.mp hm) ((mul_eq_zero.mp e.symm).resolve_left hN0)
  exact (dualWeylDominanceZ r n ν hnr hν u huD m hmu).1 k

def LehwShift {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ)
    (P : Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ δ : ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous w (P.coeff k) (μ + k * δ)

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_mul]`. Use `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun x hx => ?_)` and prove the remaining obligations. Rewrite `hx` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Use `(mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_` and prove the remaining obligations.

Establish `h` using `(hP x.1).mul (hQ x.2)`. Use `h using 1` and compare the differences between its conclusion and the goal. Rewrite using `[← hx]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem lehwShift_mul {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : ℤ}
    (hP : LehwShift w P μ δ) (hQ : LehwShift w Q μ' δ) : LehwShift w (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun x hx => ?_)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := (hP x.1).mul (hQ x.2)
  convert h using 1
  rw [← hx]
  push_cast
  ring

/- English proof (translation)
Introduce `k`. Distinguish the cases in `hk : k = 0`. Substitute `hk` using the available equality. Rewrite using `[Polynomial.coeff_one_zero]`. Introduce `d hd`.

Rewrite `hd` using `[MvPolynomial.coeff_one]`. Use `split_ifs at hd with h`. Substitute `h` using the available equality. Simplify using the standard rewrite rules. Conclude with `(hd rfl).elim`.

Rewrite using `[Polynomial.coeff_one, if_neg (by omega)]`. Introduce `d hd`. Conclude with `(hd (MvPolynomial.coeff_zero d)).elim`.
-/
theorem lehwShift_one {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ) :
    LehwShift w (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  by_cases hk : k = 0
  · subst hk
    rw [Polynomial.coeff_one_zero]
    intro d hd
    rw [MvPolynomial.coeff_one] at hd
    split_ifs at hd with h
    · subst h
      simp
    · exact (hd rfl).elim
  · rw [Polynomial.coeff_one, if_neg (by omega)]
    intro d hd
    exact (hd (MvPolynomial.coeff_zero d)).elim

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => simpa using lehwShift_one (R := R) w δ`. Consider the case `succ e ih`. Rewrite using `[pow_succ, succ_nsmul]`. Conclude with `lehwShift_mul ih hP`.
-/
theorem lehwShift_pow {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : ℤ}
    (hP : LehwShift w P μ δ) (e : ℕ) : LehwShift w (P ^ e) (e • μ) δ := by
  induction e with
  | zero => simpa using lehwShift_one (R := R) w δ
  | succ e ih =>
    rw [pow_succ, succ_nsmul]
    exact lehwShift_mul ih hP

/- English proof (translation)
Use `revert h`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Introduce `_`. Simplify using `using lehwShift_one (R := R) w δ`. Introduce `i s hi ih h`.

Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi]`. Conclude with `lehwShift_mul (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem lehwShift_prod {R : Type*} [CommRing R] {r n : ℕ} {w : Fin r × Fin n → ℤ} {ι : Type*}
    (s : Finset ι) (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → ℤ) (δ : ℤ)
    (h : ∀ i ∈ s, LehwShift w (P i) (μ i) δ) : LehwShift w (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  revert h
  refine Finset.induction_on s ?_ ?_
  · intro _
    simpa using lehwShift_one (R := R) w δ
  · intro i s hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact lehwShift_mul (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Introduce `k`. Establish `h1` using `lehwShift_one (R := R) w δ k`. Rewrite using `[Algebra.algebraMap_eq_smul_one, Polynomial.coeff_smul]`. Conclude with `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.smul_mem _ c ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1))`.
-/
theorem lehwShift_algebraMap {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (c : R) (δ : ℤ) :
    LehwShift w (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  have h1 := lehwShift_one (R := R) w δ k
  rw [Algebra.algebraMap_eq_smul_one, Polynomial.coeff_smul]
  exact (mem_weightedHomogeneousSubmodule _ _ _ _).mp
    (Submodule.smul_mem _ c ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr h1))

/- English proof (translation)
Take `⟨c, s⟩` from `v`. Introduce `k`. Distinguish the cases in `hc : c = b`. Substitute `hc` using the available equality. Rewrite using `[if_pos (show (c, s).1 = c from rfl)]`.

Break down `k with _ | _ | k` into its components or cases. Establish `e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) : Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff 0 = X (c, s)` using `by simp`. Rewrite using `[e]`. Simplify using `using isWeightedHomogeneous_X R w (c, s)`. Establish `e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) : Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (0 + 1) = X (a, s)` using `by simp`.

Rewrite using `[e]`. Use `isWeightedHomogeneous_X R w (a, s) using 1` and compare the differences between its conclusion and the goal. Rewrite using `[hstep s]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) : Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (k + 1 + 1) = 0`. Simplify using `[Polynomial.coeff_C]`. Rewrite using `[e]`. Introduce `d hd`. Conclude with `(hd (MvPolynomial.coeff_zero d)).elim`.

Rewrite using `[if_neg (show ¬ (c, s).1 = b from hc), add_zero, Polynomial.coeff_C] split_ifs with hk`. Substitute `hk` using the available equality. Simplify using `using isWeightedHomogeneous_X R w (c, s)`. Introduce `d hd`. Conclude with `(hd (MvPolynomial.coeff_zero d)).elim`.
-/
theorem lehwShift_gen {R : Type*} [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (v : Fin r × Fin n) :
    LehwShift w (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (w v) δ := by
  obtain ⟨c, s⟩ := v
  intro k
  by_cases hc : c = b
  · subst hc
    rw [if_pos (show (c, s).1 = c from rfl)]
    rcases k with _ | _ | k
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff 0 = X (c, s) := by simp
      rw [e]
      simpa using isWeightedHomogeneous_X R w (c, s)
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (0 + 1) = X (a, s) := by simp
      rw [e]
      convert isWeightedHomogeneous_X R w (a, s) using 1
      rw [hstep s]
      push_cast
      ring
    · have e : (Polynomial.C (X (c, s)) + Polynomial.X * Polynomial.C (X (a, s)) :
          Polynomial (MvPolynomial (Fin r × Fin n) R)).coeff (k + 1 + 1) = 0 := by
        simp [Polynomial.coeff_C]
      rw [e]
      intro d hd
      exact (hd (MvPolynomial.coeff_zero d)).elim
  · rw [if_neg (show ¬ (c, s).1 = b from hc), add_zero, Polynomial.coeff_C]
    split_ifs with hk
    · subst hk
      simpa using isWeightedHomogeneous_X R w (c, s)
    · intro d hd
      exact (hd (MvPolynomial.coeff_zero d)).elim

/- English proof (translation)
Unfold `rowGen`. Rewrite using `[MvPolynomial.aeval_monomial, Finsupp.weight_apply]`. Establish `h` using `lehwShift_mul (lehwShift_algebraMap (R := R) w c δ) (lehwShift_prod d.support _ (fun v => d v • w v) δ (fun v _ => lehwShift_pow (lehwShift_gen (R := R) w δ a b hstep v) (d v)))`. Simplify `h` using `[Finsupp.prod, Finsupp.sum]`.
-/
theorem lehwShift_rowGen_monomial (R : Type*) [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (d : Fin r × Fin n →₀ ℕ) (c : R) :
    LehwShift w (rowGen R a b (monomial d c)) (Finsupp.weight w d) δ := by
  unfold rowGen
  rw [MvPolynomial.aeval_monomial, Finsupp.weight_apply]
  have h := lehwShift_mul (lehwShift_algebraMap (R := R) w c δ)
    (lehwShift_prod d.support _ (fun v => d v • w v) δ
      (fun v _ => lehwShift_pow (lehwShift_gen (R := R) w δ a b hstep v) (d v)))
  simpa [Finsupp.prod, Finsupp.sum] using h

/- English proof (translation)
Unfold `rowDiv`. Rewrite using `[f.as_sum, map_sum, Polynomial.finset_sum_coeff]`. Use `(mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun d hd => ?_)` and prove the remaining obligations. Use `(mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_` and prove the remaining obligations. Establish `h` using `lehwShift_rowGen_monomial R w δ a b hstep d (coeff d f) k`.

Rewrite `h` using `[hf (mem_support_iff.mp hd)]`. Conclude with `h`.
-/
theorem lehw_rowDiv_shift (R : Type*) [CommRing R] {r n : ℕ} (w : Fin r × Fin n → ℤ) (δ : ℤ)
    (a b : Fin r) (hstep : ∀ s : Fin n, w (a, s) = w (b, s) + δ) (H : ℤ) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous w f H) :
    IsWeightedHomogeneous w (rowDiv R a b k f) (H + k * δ) := by
  unfold rowDiv
  rw [f.as_sum, map_sum, Polynomial.finset_sum_coeff]
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.sum_mem _ fun d hd => ?_)
  refine (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_
  have h := lehwShift_rowGen_monomial R w δ a b hstep d (coeff d f) k
  rw [hf (mem_support_iff.mp hd)] at h
  exact h

def lehwP {r n : ℕ} (a : Fin r) : Fin r × Fin n → ℤ := fun v => if v.1.val ≤ a.val then 1 else 0

/- English proof (translation)
Establish `h : a.val < b.val` using `hab`. Simplify using `[lehwP, show ¬ b.val ≤ a.val by omega]`.
-/
theorem highestWeightCount_self_eq_succ_of_lt {r n : ℕ} {a b : Fin r} (hab : a < b) (s : Fin n) :
    lehwP (n := n) a (a, s) = lehwP a (b, s) + 1 := by
  have h : a.val < b.val := hab
  simp [lehwP, show ¬ b.val ≤ a.val by omega]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]`. Use `push_cast`. Rewrite using `[Finset.sum_filter]`. Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Simplify using `only [rowDeg, lehwP]`.

Distinguish the cases in `h : a'.val ≤ a.val`. Simplify using `[h, show a'.val < a.val + 1 by omega]`. Simplify using `[h, show ¬ a'.val < a.val + 1 by omega]`.
-/
theorem lehw_weight_P {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) :
    Finsupp.weight (lehwP a) m = ((∑ a' : Fin r with a'.val < a.val + 1, rowDeg m a' : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_prod_type]
  push_cast
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [rowDeg, lehwP]
  by_cases h : a'.val ≤ a.val
  · simp [h, show a'.val < a.val + 1 by omega]
  · simp [h, show ¬ a'.val < a.val + 1 by omega]

/- English proof (translation)
Rewrite using `[Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]`. Simplify using `only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using `[rowDeg]`. Introduce `b _ hb`.

Simplify using `[hb, Ne.symm hb]`. Simplify using the standard rewrite rules.
-/
theorem lehw_weight_rowW {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) m a = rowDeg m a := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply,
    Fintype.sum_prod_type]
  simp only [rowW, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single a]
  · simp [rowDeg]
  · intro b _ hb
    simp [hb, Ne.symm hb]
  · simp

/- English proof (translation)
Establish `hH` using `rowDivStable ℚ r n ν a b k G hG`. Assume the negation of the conclusion as `hne`. Take `⟨m, hm⟩` from `MvPolynomial.ne_zero_iff.mp hne`. Establish `hGP : IsWeightedHomogeneous (lehwP (n` using `n) a) G ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by`. Introduce `d hd`.

Rewrite using `[lehw_weight_P]`. Use `congr 1`. Use `Finset.sum_congr rfl fun a' _ => ?_` and prove the remaining obligations. Rewrite using `[← lehw_weight_rowW, hGh hd]`. Establish `hshift` using `lehw_rowDiv_shift ℚ (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGP`.

Establish `hmw` using `hshift hm`. Rewrite `hmw` using `[lehw_weight_P]`. Establish `hdom` using `lehw_dom ν hn hν _ hH m (mem_support_iff.mpr hm) (a.val + 1)`. Use linear arithmetic over natural numbers and integers.
-/
theorem lehw_kill {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν)
    (G : MvPolynomial (Fin r × Fin n) ℚ) (hG : G ∈ dualWeyl ℚ r n ν)
    (hGh : IsWeightedHomogeneous (rowW r n) G (rowNu (r := r) ν))
    (a b : Fin r) (hab : a < b) (k : ℕ) (hk : 1 ≤ k) : rowDiv ℚ a b k G = 0 := by
  have hH := rowDivStable ℚ r n ν a b k G hG
  by_contra hne
  obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hne
  have hGP : IsWeightedHomogeneous (lehwP (n := n) a) G
      ((∑ a' : Fin r with a'.val < a.val + 1, rowNu (r := r) ν a' : ℕ) : ℤ) := by
    intro d hd
    rw [lehw_weight_P]
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    rw [← lehw_weight_rowW, hGh hd]
  have hshift := lehw_rowDiv_shift ℚ (lehwP a) 1 a b (highestWeightCount_self_eq_succ_of_lt hab) _ k G hGP
  have hmw := hshift hm
  rw [lehw_weight_P] at hmw
  have hdom := lehw_dom ν hn hν _ hH m (mem_support_iff.mpr hm) (a.val + 1)
  omega

end Formalism.GradedWeylDivisibility
