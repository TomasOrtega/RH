import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Introduce `K _ A f`. Take `⟨F, hF, hev⟩` from `GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl 2 ![𝟙 A, f]`. Use `set N := 2 * A.dim with hN`. Establish `hsupp : ∀ d ∈ F.support, d 0 + d 1 = N`. Introduce `d hd`.

Assume the negation of the conclusion as `h`. Use `(MvPolynomial.mem_support_iff.mp hd) (hF.coeff_eq_zero ?_)` and prove the remaining obligations. Rewrite using `[Finsupp.degree_eq_sum, Fin.sum_univ_two]` and apply the resulting hypothesis. Set `P : Polynomial ℚ` to `∑ d ∈ F.support, Polynomial.C (MvPolynomial.coeff d F * (-1) ^ d 1) * Polynomial.X ^ d 0`. Establish `hPeval : ∀ q : ℚ, P.eval q = MvPolynomial.eval ![q, -1] F`.

Introduce `q`. Rewrite using `[MvPolynomial.eval_eq', Polynomial.eval_finsetSum]`. Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Simplify using `[Fin.prod_univ_two]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hcoef : P.coeff N = MvPolynomial.coeff (Finsupp.single 0 N) F`. Rewrite using `[Polynomial.finsetSum_coeff]`. Simplify using `only [Polynomial.coeff_C_mul_X_pow]`. Rewrite using `[Finset.sum_eq_single (Finsupp.single 0 N)]`. Simplify using the standard rewrite rules.

Introduce `d hd hne`. Rewrite using `[if_neg]`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Use `hsupp d hd` as an intermediate fact.

Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp <;> omega`. Introduce `h`. Simplify using `[MvPolynomial.notMem_support_iff.mp h]`. Establish `hdeg : P.natDegree ≤ N`.

Apply `Polynomial.natDegree_sum_le_of_forall_le` to reduce the goal to its premises. Introduce `d hd`. Conclude with `(Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := hsupp d hd; omega)`. Establish `h10 : MvPolynomial.eval ![1, 0] F = MvPolynomial.coeff (Finsupp.single 0 N) F`. Rewrite using `[MvPolynomial.eval_eq', Finset.sum_eq_single (Finsupp.single 0 N)]`.

Simplify using `[Fin.prod_univ_two]`. Introduce `d hd hne`. Use `hsupp d hd` as an intermediate fact. Establish `h1 : d 1 ≠ 0`. Introduce `h1`.

Apply `hne` to reduce the goal to its premises. Use extensionality with `i`. Apply the tactic sequence `fin_cases i <;> simp <;> omega`. Simplify using `[Fin.prod_univ_two, h1]`. Introduce `h`.

Simplify using `[MvPolynomial.notMem_support_iff.mp h]`. Establish `hone : MvPolynomial.eval ![1, 0] F = 1`. Establish `h` using `hev ![1, 0]`. Establish `e1 : (fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![1, 0]`. Apply the tactic sequence `ext i; fin_cases i <;> simp`.

Rewrite `h` using `[e1]`. Rewrite using `[h]`. Establish `h2` using `(GlobalTheory.MulIsogeny.mul_isogeny K A 1 one_ne_zero).2`. Simplify using `only [one_smul, Int.natAbs_one, one_pow] at h2`. Simplify using `[Fin.sum_univ_two, h2]`.

Establish `hnat : P.natDegree = N`. Apply `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg` to reduce the goal to its premises. Rewrite using `[hcoef, ← h10, hone]`. Conclude with `one_ne_zero`. Use `⟨P, ?_, hnat, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.Monic, Polynomial.leadingCoeff, hnat, hcoef, ← h10, hone]`. Introduce `n`. Rewrite using `[hPeval]`. Establish `h` using `hev ![n, -1]`. Establish `e1 : (fun i => (((![n, -1] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![(n : ℚ), -1]`.

Apply the tactic sequence `ext i; fin_cases i <;> simp`. Rewrite `h` using `[e1]`. Rewrite using `[h]`. Use `congr 2`. Rewrite using `[Fin.sum_univ_two]`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, neg_smul, one_smul]`. Rewrite using `[sub_eq_add_neg]`. Use `congr 1`. Conclude with `zsmul_one (R := End A) n`.
-/
theorem GlobalTheory.charPolyRat : ∀ (K : Type) [Field K] (A : AbVar K) (f : End A), ∃ P : Polynomial ℚ, P.Monic ∧ P.natDegree = 2 * A.dim ∧ ∀ n : ℤ, P.eval (n : ℚ) = (deg (A := A) (B := A) ((n : End A) - f) : ℚ) := by
  intro K _ A f
  obtain ⟨F, hF, hev⟩ := GlobalTheory.T.homDegree_integerCombination_isHomogeneous K A A rfl 2 ![𝟙 A, f]
  set N := 2 * A.dim with hN
  have hsupp : ∀ d ∈ F.support, d 0 + d 1 = N := by
    intro d hd
    by_contra h
    refine (MvPolynomial.mem_support_iff.mp hd) (hF.coeff_eq_zero ?_)
    rwa [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  let P : Polynomial ℚ := ∑ d ∈ F.support,
    Polynomial.C (MvPolynomial.coeff d F * (-1) ^ d 1) * Polynomial.X ^ d 0
  have hPeval : ∀ q : ℚ, P.eval q = MvPolynomial.eval ![q, -1] F := by
    intro q
    rw [MvPolynomial.eval_eq', Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp [Fin.prod_univ_two]
    ring
  have hcoef : P.coeff N = MvPolynomial.coeff (Finsupp.single 0 N) F := by
    rw [Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp
    · intro d hd hne
      rw [if_neg]
      intro h0
      apply hne
      have := hsupp d hd
      ext i
      fin_cases i <;> simp <;> omega
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hdeg : P.natDegree ≤ N := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro d hd
    exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (by have := hsupp d hd; omega)
  have h10 : MvPolynomial.eval ![1, 0] F = MvPolynomial.coeff (Finsupp.single 0 N) F := by
    rw [MvPolynomial.eval_eq', Finset.sum_eq_single (Finsupp.single 0 N)]
    · simp [Fin.prod_univ_two]
    · intro d hd hne
      have := hsupp d hd
      have h1 : d 1 ≠ 0 := by
        intro h1
        apply hne
        ext i
        fin_cases i <;> simp <;> omega
      simp [Fin.prod_univ_two, h1]
    · intro h
      simp [MvPolynomial.notMem_support_iff.mp h]
  have hone : MvPolynomial.eval ![1, 0] F = 1 := by
    have h := hev ![1, 0]
    have e1 : (fun i => (((![1, 0] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![1, 0] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    have h2 := (GlobalTheory.MulIsogeny.mul_isogeny K A 1 one_ne_zero).2
    simp only [one_smul, Int.natAbs_one, one_pow] at h2
    simp [Fin.sum_univ_two, h2]
  have hnat : P.natDegree = N := by
    apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg
    rw [hcoef, ← h10, hone]
    exact one_ne_zero
  refine ⟨P, ?_, hnat, ?_⟩
  · rw [Polynomial.Monic, Polynomial.leadingCoeff, hnat, hcoef, ← h10, hone]
  · intro n
    rw [hPeval]
    have h := hev ![n, -1]
    have e1 : (fun i => (((![n, -1] : Fin 2 → ℤ) i : ℤ) : ℚ)) = ![(n : ℚ), -1] := by
      ext i; fin_cases i <;> simp
    rw [e1] at h
    rw [h]
    congr 2
    rw [Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, neg_smul, one_smul]
    rw [sub_eq_add_neg]
    congr 1
    exact zsmul_one (R := End A) n
