import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapLine

set_option autoImplicit false

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDisc

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert p s hp ih`. Establish `h1 : (v p ^ m p).natDegree ≤ m p * w p` using `Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (h p))`. Rewrite using `[Finset.prod_insert hp, Finset.sum_insert hp, Finset.prod_insert hp]`.

Use `⟨Polynomial.natDegree_mul_le.trans (add_le_add h1 ih.1), ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih.1, ih.2, Polynomial.coeff_pow_of_natDegree_le (h p)]`.
-/
theorem prod_pow_natDegree_le_and_coeff {R ι : Type} [CommRing R] (s : Finset ι) (v : ι → Polynomial R) (w m : ι → ℕ)
    (h : ∀ p, (v p).natDegree ≤ w p) :
    (∏ p ∈ s, v p ^ m p).natDegree ≤ ∑ p ∈ s, m p * w p ∧
      (∏ p ∈ s, v p ^ m p).coeff (∑ p ∈ s, m p * w p) = ∏ p ∈ s, (v p).coeff (w p) ^ m p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih =>
    have h1 : (v p ^ m p).natDegree ≤ m p * w p :=
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (h p))
    rw [Finset.prod_insert hp, Finset.sum_insert hp, Finset.prod_insert hp]
    refine ⟨Polynomial.natDegree_mul_le.trans (add_le_add h1 ih.1), ?_⟩
    rw [Polynomial.coeff_mul_add_eq_of_natDegree_le h1 ih.1, ih.2,
      Polynomial.coeff_pow_of_natDegree_le (h p)]

/- English proof (translation)
Use `set v : Fin (D + 1) × Fin N → Polynomial R := join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X with hv`. Set `w : Fin (D + 1) × Fin N → ℕ` to `fun p => if p.1 = Fin.last D then 1 else 0`. Establish `hdeg : ∀ p, (v p).natDegree ≤ w p`. Introduce and unpack `⟨i, j⟩`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations.

Simplify using `only [hv, w, join, if_true, Fin.lastCases_last]`. Rewrite using `[add_comm]`. Conclude with `Polynomial.natDegree_linear_le`. Simplify using `[hv, w, join]`. Establish `hco : ∀ p, (v p).coeff (w p) = join u b p`.

Introduce and unpack `⟨i, j⟩`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[hv, w, join]`. Simplify using `[hv, w, join]`. Establish `hsum : ∀ m ∈ f.support, ∑ p, m p * w p = δ`.

Introduce `m hm`. Use `hf m (by simpa using hm) (Fin.last D)` as an intermediate fact. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]`. Simplify `this` using `[w]`. Introduce `i _ hi`.

Simplify using `[w, hi]`. Simplify using the standard rewrite rules. Establish `hkey : ∀ m ∈ f.support, (∏ p, v p ^ m p).natDegree ≤ δ ∧ (∏ p, v p ^ m p).coeff δ = ∏ p, join u b p ^ m p`. Introduce `m hm`. Use `prod_pow_natDegree_le_and_coeff Finset.univ v w m hdeg` as an intermediate fact.

Rewrite `this` using `[hsum m hm]`. Simplify `this` using `only [hco]`. Establish `hline : line u a b f = ∑ m ∈ f.support, Polynomial.C (algebraMap F R (f.coeff m)) * ∏ p, v p ^ m p`. Rewrite using `[line, ← hv, aeval_def, eval₂_eq']`. Both sides reduce to the same expression.

Rewrite using `[hline, aeval_def, eval₂_eq']`. Use `⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm => (Polynomial.natDegree_C_mul_le _ _).trans (hkey m hm).1, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.finset_sum_coeff]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.coeff_C_mul, (hkey m hm).2]`.
-/
theorem line_natDegree_le_and_coeff (F R : Type) [CommRing F] [CommRing R] [Algebra F R] (D N δ : ℕ)
    (f : MvPolynomial (Fin (D + 1) × Fin N) F) (hf : IsMultiHomogeneous (fun _ => δ) f)
    (u : Fin D → Fin N → R) (a b : Fin N → R) :
    (GlobalTheory.PencilDisc.line u a b f).natDegree ≤ δ ∧
      (GlobalTheory.PencilDisc.line u a b f).coeff δ = MvPolynomial.aeval (GlobalTheory.HSChoice.join u b) f := by
  classical
  set v : Fin (D + 1) × Fin N → Polynomial R :=
    join (fun i j => Polynomial.C (u i j)) fun j => Polynomial.C (a j) + Polynomial.C (b j) * Polynomial.X with hv
  let w : Fin (D + 1) × Fin N → ℕ := fun p => if p.1 = Fin.last D then 1 else 0
  have hdeg : ∀ p, (v p).natDegree ≤ w p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [hv, w, join, if_true, Fin.lastCases_last]
      rw [add_comm]
      exact Polynomial.natDegree_linear_le
    · simp [hv, w, join]
  have hco : ∀ p, (v p).coeff (w p) = join u b p := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp [hv, w, join]
    · simp [hv, w, join]
  have hsum : ∀ m ∈ f.support, ∑ p, m p * w p = δ := by
    intro m hm
    have := hf m (by simpa using hm) (Fin.last D)
    rw [Fintype.sum_prod_type, Finset.sum_eq_single (Fin.last D)]
    · simpa [w] using this
    · intro i _ hi
      simp [w, hi]
    · simp
  have hkey : ∀ m ∈ f.support, (∏ p, v p ^ m p).natDegree ≤ δ ∧
      (∏ p, v p ^ m p).coeff δ = ∏ p, join u b p ^ m p := by
    intro m hm
    have := prod_pow_natDegree_le_and_coeff Finset.univ v w m hdeg
    rw [hsum m hm] at this
    simpa only [hco] using this
  have hline : line u a b f =
      ∑ m ∈ f.support, Polynomial.C (algebraMap F R (f.coeff m)) * ∏ p, v p ^ m p := by
    rw [line, ← hv, aeval_def, eval₂_eq']
    rfl
  rw [hline, aeval_def, eval₂_eq']
  refine ⟨Polynomial.natDegree_sum_le_of_forall_le _ _ fun m hm =>
    (Polynomial.natDegree_C_mul_le _ _).trans (hkey m hm).1, ?_⟩
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [Polynomial.coeff_C_mul, (hkey m hm).2]

end GlobalTheory.PencilDisc
