import Mathlib
open scoped TensorProduct

namespace GlobalTheory

open MvPolynomial

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C b`. Rewrite using `[aeval_C, pderiv_C, map_zero]`. Conclude with `hB i _ b.2`. Consider the case `add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]`.

Consider the case `mul_X p j hp`. Establish `h1 : E i (aeval x p * x j) = aeval x p * E i (x j) + x j * E i (aeval x p)`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul]`. Rewrite using `[map_mul, aeval_X, h1, hp, pderiv_mul, pderiv_X, map_add, map_mul, map_mul, aeval_X, hE]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h, Pi.single_apply, Ne.symm h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem truncMono_deriv_aeval {k A : Type} [Field k] [CommRing A] [Algebra k A] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) (i : Fin d) (F : MvPolynomial (Fin d) B) :
    E i (aeval x F) = aeval x (pderiv i F) := by
  induction F using MvPolynomial.induction_on with
  | C b =>
    rw [aeval_C, pderiv_C, map_zero]
    exact hB i _ b.2
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add]
  | mul_X p j hp =>
    have h1 : E i (aeval x p * x j) = aeval x p * E i (x j) + x j * E i (aeval x p) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [map_mul, aeval_X, h1, hp, pderiv_mul, pderiv_X, map_add, map_mul, map_mul, aeval_X, hE]
    by_cases h : i = j
    · subst h; simp; ring
    · simp [h, Pi.single_apply, Ne.symm h]; ring

/- English proof (translation)
Establish `hconst : ∀ F : MvPolynomial (Fin d) B, (∀ m, m ≠ 0 → coeff m F = 0) → aeval x F = 0 → F = 0`. Introduce `F hc hF`. Establish `hFC : F = C (coeff 0 F)`. Use `MvPolynomial.ext _ _ (fun m => ?_)` and prove the remaining obligations. Rewrite using `[coeff_C]`.

Distinguish the cases in `hm : m = 0`. Substitute `hm` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg (Ne.symm hm)]`. Conclude with `hc m hm`.

Rewrite `hF` using `[hFC, aeval_C]`. Establish `h0 : coeff 0 F = 0` using `Subtype.ext (by simpa using hF)`. Rewrite using `[hFC, h0, C_0]`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero`. Introduce `F hs hF`. Apply `hconst F _ hF` to reduce the goal to its premises. Introduce `m hm`. Assume the negation of the conclusion as `hc`.

Use `(hs m (mem_support_iff.mpr hc)).2` as an intermediate fact. Apply `hm` to reduce the goal to its premises. Use extensionality with `i`. Use `(Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp this)) i (Finset.mem_univ _)` as an intermediate fact. Simplify using `using this`.

Consider the case `succ n ih`. Introduce `F hs hF`. Establish `hpd : ∀ i, pderiv i F = 0`. Introduce `i`. Apply `ih` to reduce the goal to its premises.

Introduce `m hm`. Rewrite `hm` using `[mem_support_iff, coeff_pderiv]`. Establish `hm'` using `hs _ (mem_support_iff.mpr (left_ne_zero_of_mul hm))`. Use `⟨fun j => lt_of_le_of_lt ?_ (hm'.1 j), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules.

Establish `h2` using `hm'.2`. Simplify using `only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib] at h2`. Establish `h3 : ∑ j, (Finsupp.single i 1 : Fin d →₀ ℕ) j = 1`. Simplify using `[Finsupp.single_apply]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[← truncMono_deriv_aeval x E hE B hB, hF, map_zero]`. Apply `hconst F _ hF` to reduce the goal to its premises. Introduce `m hm`. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, m i ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hm (Finsupp.ext h)`. Assume the negation of the conclusion as `hc`. Establish `hlt` using `(hs m (mem_support_iff.mpr hc)).1 i`. Establish `hcoef` using `coeff_pderiv (i := i) F (m - Finsupp.single i 1)`.

Rewrite `hcoef` using `[Finsupp.sub_add_single_one_cancel hi, hpd i, coeff_zero]`. Establish `hmi : (m - Finsupp.single i 1 : Fin d →₀ ℕ) i + 1 = m i`. Simplify using `only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]`. Use linear arithmetic over natural numbers and integers. Establish `hunit : IsUnit (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1)`.

Establish `e : (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) = algebraMap k B ((m i : ℕ) : k)`. Rewrite using `[map_natCast, ← hmi]`. Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[e]`.

Apply `IsUnit.map` to reduce the goal to its premises. Apply `Ne.isUnit` to reduce the goal to its premises. Rewrite using `[Ne, CharP.cast_eq_zero_iff k p]`. Introduce `hdvd`. Conclude with `hi (Nat.eq_zero_of_dvd_of_lt hdvd hlt)`.

Conclude with `hc ((hunit.mul_left_eq_zero).mp hcoef.symm)`.
-/
theorem truncMono_eq_zero {p : ℕ} [Fact p.Prime] {k A : Type} [Field k] [CommRing A]
    [Algebra k A] [CharP k p] {d : ℕ}
    (x : Fin d → A) (E : Fin d → Derivation k A A)
    (hE : ∀ i j, E i (x j) = if i = j then 1 else 0) (B : Subalgebra k A)
    (hB : ∀ i, ∀ b ∈ B, E i b = 0) :
    ∀ n : ℕ, ∀ F : MvPolynomial (Fin d) B,
      (∀ m ∈ F.support, (∀ i, m i < p) ∧ ∑ i, m i ≤ n) → aeval x F = 0 → F = 0 := by
  have hconst : ∀ F : MvPolynomial (Fin d) B, (∀ m, m ≠ 0 → coeff m F = 0) →
      aeval x F = 0 → F = 0 := by
    intro F hc hF
    have hFC : F = C (coeff 0 F) := by
      refine MvPolynomial.ext _ _ (fun m => ?_)
      rw [coeff_C]
      by_cases hm : m = 0
      · subst hm; simp
      · rw [if_neg (Ne.symm hm)]; exact hc m hm
    rw [hFC, aeval_C] at hF
    have h0 : coeff 0 F = 0 := Subtype.ext (by simpa using hF)
    rw [hFC, h0, C_0]
  intro n
  induction n with
  | zero =>
    intro F hs hF
    apply hconst F _ hF
    intro m hm
    by_contra hc
    have := (hs m (mem_support_iff.mpr hc)).2
    apply hm
    ext i
    have := (Finset.sum_eq_zero_iff.mp (Nat.le_zero.mp this)) i (Finset.mem_univ _)
    simpa using this
  | succ n ih =>
    intro F hs hF
    have hpd : ∀ i, pderiv i F = 0 := by
      intro i
      apply ih
      · intro m hm
        rw [mem_support_iff, coeff_pderiv] at hm
        have hm' := hs _ (mem_support_iff.mpr (left_ne_zero_of_mul hm))
        refine ⟨fun j => lt_of_le_of_lt ?_ (hm'.1 j), ?_⟩
        · simp
        · have h2 := hm'.2
          simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib] at h2
          have h3 : ∑ j, (Finsupp.single i 1 : Fin d →₀ ℕ) j = 1 := by
            simp [Finsupp.single_apply]
          omega
      · rw [← truncMono_deriv_aeval x E hE B hB, hF, map_zero]
    apply hconst F _ hF
    intro m hm
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hm (Finsupp.ext h)
    by_contra hc
    have hlt := (hs m (mem_support_iff.mpr hc)).1 i
    have hcoef := coeff_pderiv (i := i) F (m - Finsupp.single i 1)
    rw [Finsupp.sub_add_single_one_cancel hi, hpd i, coeff_zero] at hcoef
    have hmi : (m - Finsupp.single i 1 : Fin d →₀ ℕ) i + 1 = m i := by
      simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]; omega
    have hunit : IsUnit (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) := by
      have e : (((m - Finsupp.single i 1 : Fin d →₀ ℕ) i : B) + 1) = algebraMap k B ((m i : ℕ) : k) := by
        rw [map_natCast, ← hmi]; push_cast; rfl
      rw [e]
      apply IsUnit.map
      apply Ne.isUnit
      rw [Ne, CharP.cast_eq_zero_iff k p]
      intro hdvd
      exact hi (Nat.eq_zero_of_dvd_of_lt hdvd hlt)
    exact hc ((hunit.mul_left_eq_zero).mp hcoef.symm)

end GlobalTheory

namespace GlobalTheory
open MvPolynomial

/- English proof (translation)
Introduce `p _ k A _ _ _ _ d x E hE B hB`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Set `toF : (Fin d → Fin p) → (Fin d →₀ ℕ)` to `fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))`. Establish `hinj : Function.Injective toF`.

Introduce `a b hab`. Use function extensionality and compare the values at `i`. Apply `Fin.ext` to reduce the goal to its premises. Use `congrArg (fun f : Fin d →₀ ℕ => f i) hab` as an intermediate fact. Simplify `this` using `[toF]`.

Set `F : MvPolynomial (Fin d) B` to `∑ a, monomial (toF a) (g a)`. Establish `hcoeff : ∀ m, coeff m F = ∑ a, if toF a = m then g a else 0`. Introduce `m`. Simplify using `only [F, coeff_sum, coeff_monomial]`. Establish `hF : aeval x F = 0`.

Rewrite using `[← hg]`. Simplify using `only [F, map_sum, aeval_monomial]`. Use `Finset.sum_congr rfl (fun a _ => ?_)` and prove the remaining obligations. Rewrite using `[Finsupp.prod_fintype _ _ (fun i => pow_zero _), Subalgebra.smul_def]`. Both sides reduce to the same expression.

Establish `hF0 : F = 0`. Use `truncMono_eq_zero x E hE B hB (∑ _i : Fin d, p) F ?_ hF` and prove the remaining obligations. Introduce `m hm`. Rewrite `hm` using `[mem_support_iff, hcoeff]`. Take `⟨a, _, ha⟩` from `Finset.exists_ne_zero_of_sum_ne_zero hm`.

Establish `hm' : toF a = m`. Assume the negation of the conclusion as `h`. Conclude with `ha (if_neg h)`. Substitute `hm'` using the available equality. Use `⟨fun i => by simp [toF], ?_⟩` and prove the remaining obligations.

Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `i _`. Simplify using `[toF, (a i).isLt.le]`. Introduce `a`. Use `hcoeff (toF a)` as an intermediate fact.

Rewrite `this` using `[hF0, coeff_zero]`. Rewrite `this` using `[hinj.eq_iff]`. Simplify using `using this.symm`.
-/
theorem truncMono_linearIndependent : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] (d : ℕ) (x : Fin d → A) (E : Fin d → Derivation k A A), (∀ i j, E i (x j) = if i = j then 1 else 0) → ∀ B : Subalgebra k A, (∀ i, ∀ b ∈ B, E i b = 0) → LinearIndependent B (fun a : Fin d → Fin p => ∏ i, x i ^ (a i : ℕ)) := by
  intro p _ k A _ _ _ _ d x E hE B hB
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let toF : (Fin d → Fin p) → (Fin d →₀ ℕ) := fun a => Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ))
  have hinj : Function.Injective toF := by
    intro a b hab
    funext i
    apply Fin.ext
    have := congrArg (fun f : Fin d →₀ ℕ => f i) hab
    simpa [toF] using this
  let F : MvPolynomial (Fin d) B := ∑ a, monomial (toF a) (g a)
  have hcoeff : ∀ m, coeff m F = ∑ a, if toF a = m then g a else 0 := by
    intro m
    simp only [F, coeff_sum, coeff_monomial]
  have hF : aeval x F = 0 := by
    rw [← hg]
    simp only [F, map_sum, aeval_monomial]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Subalgebra.smul_def]
    rfl
  have hF0 : F = 0 := by
    refine truncMono_eq_zero x E hE B hB (∑ _i : Fin d, p) F ?_ hF
    intro m hm
    rw [mem_support_iff, hcoeff] at hm
    obtain ⟨a, _, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hm
    have hm' : toF a = m := by
      by_contra h
      exact ha (if_neg h)
    subst hm'
    refine ⟨fun i => by simp [toF], ?_⟩
    apply Finset.sum_le_sum
    intro i _
    simp [toF, (a i).isLt.le]
  intro a
  have := hcoeff (toF a)
  rw [hF0, coeff_zero] at this
  simp_rw [hinj.eq_iff] at this
  simpa using this.symm

end GlobalTheory
