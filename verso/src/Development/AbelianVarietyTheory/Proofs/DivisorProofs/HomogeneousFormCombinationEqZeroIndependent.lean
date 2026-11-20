import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.HomInj

/- English proof (translation)
Use `conv_lhs => rw [P.as_sum]`. Use `conv_rhs => rw [P.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Establish `hd` using `hP (mem_support_iff.mp hm)`.

Simplify using `only [aeval_monomial, mul_pow]`. Rewrite using `[Finsupp.prod_mul, ← hd]`. Establish `: (m.prod fun _ k => c ^ k) = c ^ (Finsupp.weight 1 m)`. Simplify using `[Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum]`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem aeval_mul_hom {σ R A : Type} [CommRing R] [CommRing A] [Algebra R A] {P : MvPolynomial σ R} {q : ℕ} (hP : P.IsHomogeneous q)
    (c : A) (z : σ → A) : aeval (fun i => c * z i) P = c ^ q * aeval z P := by
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd := hP (mem_support_iff.mp hm)
  simp only [aeval_monomial, mul_pow]
  rw [Finsupp.prod_mul, ← hd]
  have : (m.prod fun _ k => c ^ k) = c ^ (Finsupp.weight 1 m) := by
    simp [Finsupp.prod, Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum]
  rw [this]; ring

def dehom (D : ℕ) : MvPolynomial (Fin (D + 1)) ℤ →ₐ[ℤ] MvPolynomial (Fin D) ℤ :=
  aeval (Fin.cons 1 X)

/- English proof (translation)
Rewrite using `[dehom, ← AlgHom.comp_apply, comp_aeval]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `refine Fin.cases ?_ (fun j => ?_) i <;> simp`.
-/
theorem aeval_dehom {A : Type} [CommRing A] [Algebra ℤ A] {D : ℕ} (w : Fin D → A) (P : MvPolynomial (Fin (D + 1)) ℤ) :
    aeval w (dehom D P) = aeval (Fin.cons 1 w : Fin (D + 1) → A) P := by
  rw [dehom, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/- English proof (translation)
Set `R` to `MvPolynomial (Fin (D + 1)) ℤ`. Set `F` to `FractionRing R`. Establish `hinj : Function.Injective (algebraMap R F)` using `IsFractionRing.injective R F`. Use `set c : F := algebraMap R F (X 0) with hc`. Establish `hc0 : c ≠ 0`.

Rewrite using `[hc, Ne, ← map_zero (algebraMap R F)]`. Conclude with `fun e => X_ne_zero (R := ℤ) (0 : Fin (D + 1)) (hinj e)`. Set `z : Fin (D + 1) → F` to `fun i => algebraMap R F (X i) / c`. Establish `hz : (fun i => algebraMap R F (X i)) = fun i => c * z i`. Use function extensionality and compare the values at `i`.

Conclude with `(mul_div_cancel₀ _ hc0).symm`. Establish `hz0 : z = Fin.cons 1 (fun j => z j.succ)`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Use `show algebraMap R F (X 0) / c = 1`.

Conclude with `div_self hc0`. Simplify using the standard rewrite rules. Establish `key : algebraMap R F P = c ^ q * aeval z P`. Establish `e1 : algebraMap R F P = aeval (fun i => algebraMap R F (X i)) P`. Rewrite using `[← Function.comp_def (algebraMap R F) X, aeval_algebraMap_apply, aeval_X_left_apply]`.

Rewrite using `[e1, hz]`. Conclude with `aeval_mul_hom hP c z`. Establish `hzP : aeval z P = 0`. Establish `e2` using `aeval_dehom (fun j => z j.succ) P`. Rewrite `e2` using `[h, map_zero]`.

Rewrite using `[hz0]`. Conclude with `e2.symm`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[key, hzP, mul_zero, map_zero]`.
-/
theorem dehom_eq_zero {D q : ℕ} {P : MvPolynomial (Fin (D + 1)) ℤ} (hP : P.IsHomogeneous q)
    (h : dehom D P = 0) : P = 0 := by
  let R := MvPolynomial (Fin (D + 1)) ℤ
  let F := FractionRing R
  have hinj : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  set c : F := algebraMap R F (X 0) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, Ne, ← map_zero (algebraMap R F)]
    exact fun e => X_ne_zero (R := ℤ) (0 : Fin (D + 1)) (hinj e)
  let z : Fin (D + 1) → F := fun i => algebraMap R F (X i) / c
  have hz : (fun i => algebraMap R F (X i)) = fun i => c * z i := by
    funext i; exact (mul_div_cancel₀ _ hc0).symm
  have hz0 : z = Fin.cons 1 (fun j => z j.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · show algebraMap R F (X 0) / c = 1
      exact div_self hc0
    · simp
  have key : algebraMap R F P = c ^ q * aeval z P := by
    have e1 : algebraMap R F P = aeval (fun i => algebraMap R F (X i)) P := by
      rw [← Function.comp_def (algebraMap R F) X, aeval_algebraMap_apply, aeval_X_left_apply]
    rw [e1, hz]
    exact aeval_mul_hom hP c z
  have hzP : aeval z P = 0 := by
    have e2 := aeval_dehom (fun j => z j.succ) P
    rw [h, map_zero] at e2
    rw [hz0]; exact e2.symm
  apply hinj
  rw [key, hzP, mul_zero, map_zero]

end GlobalTheory.HSAmp.HomInj

namespace GlobalTheory.HSAmp

open GlobalTheory.HSAmp.HomInj in

/- English proof (translation)
Introduce `K _ _ D x hx hind _ ι _ g hg q T hT hsum`. Set `y : Fin (D + 1) → K` to `fun j => x j / x 0`. Establish `hy : ∀ j, y j ∈ ratF x`. Introduce `j`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations.

Simplify using `only [y, div_self (hx 0)]`. Conclude with `(ratF x).one_mem`. Conclude with `Subfield.subset_closure ⟨j, rfl⟩`. Set `y' : Fin (D + 1) → ratF x` to `fun j => ⟨y j, hy j⟩`. Establish `hxy : x = fun j => x 0 * y j`.

Use function extensionality and compare the values at `j`. Conclude with `(mul_div_cancel₀ _ (hx 0)).symm`. Establish `hval : ∀ i, aeval y (T i) = ((aeval y' (T i) : ratF x) : K)`. Introduce `i`. Use `show _ = algebraMap (ratF x) K _`.

Rewrite using `[← aeval_algebraMap_apply]`. Both sides reduce to the same expression. Establish `h1 : ∀ i, aeval x (T i) = x 0 ^ q * aeval y (T i)`. Introduce `i`. Rewrite using `[← aeval_mul_hom (hT i) (x 0) y]`.

Conclude with `congrArg (fun v => aeval v (T i)) hxy`. Establish `hsum' : ∑ i, aeval y' (T i) • g i = 0`. Establish `hq : x 0 ^ q ≠ 0` using `pow_ne_zero _ (hx 0)`. Establish `: x 0 ^ q * ∑ i, aeval y' (T i) • g i = 0`. Rewrite using `[Finset.mul_sum, ← hsum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h1, hval, Subfield.smul_def, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_eq_zero.mp this).resolve_left hq`. Establish `h0 : ∀ i, aeval y (T i) = 0`.

Introduce `i`. Rewrite using `[hval, Fintype.linearIndependent_iff.1 hg _ hsum' i]`. Both sides reduce to the same expression. Establish `hy0 : y = Fin.cons 1 (fun j : Fin D => x j.succ / x 0)`. Use function extensionality and compare the values at `j`.

Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `[y, div_self (hx 0)]`. Simplify using `[y]`. Use function extensionality and compare the values at `i`. Apply `dehom_eq_zero (hT i)` to reduce the goal to its premises.

Apply `(algebraicIndependent_iff_injective_aeval.1 hind)` to reduce the goal to its premises. Rewrite using `[aeval_dehom, ← hy0, h0, map_zero]`.
-/
theorem homogComb_eq_zero : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K), (∀ j, x j ≠ 0) →
    AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) → FiniteDimensional (ratF x) K →
    ∀ (ι : Type) [Fintype ι] (g : ι → K), LinearIndependent (ratF x) g → ∀ (q : ℕ)
    (T : ι → MvPolynomial (Fin (D + 1)) ℤ), (∀ i, (T i).IsHomogeneous q) → ∑ i, aeval x (T i) * g i = 0 → T = 0 := by
  intro K _ _ D x hx hind _ ι _ g hg q T hT hsum
  let y : Fin (D + 1) → K := fun j => x j / x 0
  have hy : ∀ j, y j ∈ ratF x := by
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [y, div_self (hx 0)]; exact (ratF x).one_mem
    · exact Subfield.subset_closure ⟨j, rfl⟩
  let y' : Fin (D + 1) → ratF x := fun j => ⟨y j, hy j⟩
  have hxy : x = fun j => x 0 * y j := by
    funext j; exact (mul_div_cancel₀ _ (hx 0)).symm
  have hval : ∀ i, aeval y (T i) = ((aeval y' (T i) : ratF x) : K) := by
    intro i
    show _ = algebraMap (ratF x) K _
    rw [← aeval_algebraMap_apply]
    rfl
  have h1 : ∀ i, aeval x (T i) = x 0 ^ q * aeval y (T i) := by
    intro i
    rw [← aeval_mul_hom (hT i) (x 0) y]
    exact congrArg (fun v => aeval v (T i)) hxy
  have hsum' : ∑ i, aeval y' (T i) • g i = 0 := by
    have hq : x 0 ^ q ≠ 0 := pow_ne_zero _ (hx 0)
    have : x 0 ^ q * ∑ i, aeval y' (T i) • g i = 0 := by
      rw [Finset.mul_sum, ← hsum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [h1, hval, Subfield.smul_def, smul_eq_mul]; ring
    exact (mul_eq_zero.mp this).resolve_left hq
  have h0 : ∀ i, aeval y (T i) = 0 := by
    intro i
    rw [hval, Fintype.linearIndependent_iff.1 hg _ hsum' i]; rfl
  have hy0 : y = Fin.cons 1 (fun j : Fin D => x j.succ / x 0) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [y, div_self (hx 0)]
    · simp [y]
  funext i
  apply dehom_eq_zero (hT i)
  apply (algebraicIndependent_iff_injective_aeval.1 hind)
  rw [aeval_dehom, ← hy0, h0, map_zero]

end GlobalTheory.HSAmp
