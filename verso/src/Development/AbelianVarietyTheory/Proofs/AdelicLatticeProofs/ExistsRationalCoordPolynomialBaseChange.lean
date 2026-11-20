import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

/- English proof (translation)
Establish `hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q)` using `fun q => DFunLike.congr_fun (RingHom.ext_rat ((algebraMap F A).comp (algebraMap ℚ F)) ((algebraMap R A).comp (algebraMap ℚ R))) q`. Establish `hsum : algebraMap F A a = ∑ i, algebraMap ℚ R (ω.repr a i) • b i` using `by conv_lhs => rw [← ω.sum_repr a]`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def (ω.repr a i) (ω i), map_mul, hq, hb, Algebra.smul_def (algebraMap ℚ R (ω.repr a i))]`.

Rewrite using `[hsum, b.repr_sum_self]`.
-/
theorem repr_algebraMap_of_basis_eq {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (a : F) (k : β) :
    b.repr (algebraMap F A a) k = algebraMap ℚ R (ω.repr a k) := by
  have hq : ∀ q : ℚ, algebraMap F A (algebraMap ℚ F q) = algebraMap R A (algebraMap ℚ R q) :=
    fun q => DFunLike.congr_fun (RingHom.ext_rat ((algebraMap F A).comp (algebraMap ℚ F))
      ((algebraMap R A).comp (algebraMap ℚ R))) q
  have hsum : algebraMap F A a = ∑ i, algebraMap ℚ R (ω.repr a i) • b i := by
    conv_lhs => rw [← ω.sum_repr a]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def (ω.repr a i) (ω i), map_mul, hq, hb,
      Algebra.smul_def (algebraMap ℚ R (ω.repr a i))]
  rw [hsum, b.repr_sum_self]

/- English proof (translation)
Establish `e : ∀ i j, b.repr ((b.repr u i • b i) * (b.repr v j • b j)) k = b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k)`. Introduce `i j`. Rewrite using `[smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, hb i, hb j, ← map_mul, repr_algebraMap_of_basis_eq ω b hb]`. Use `conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]`. Simplify using `only [Finset.sum_mul, Finset.mul_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, e]`.

Conclude with `Finset.sum_comm`.
-/
private theorem basis_repr_mul_of_basis_eq_algebraMap {F β : Type} [Field F] [Algebra ℚ F] [Fintype β]
    (ω : Module.Basis β ℚ F) {R A : Type} [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A]
    [Algebra F A] (b : Module.Basis β R A) (hb : ∀ i, b i = algebraMap F A (ω i)) (u v : A)
    (k : β) : b.repr (u * v) k =
      ∑ i, ∑ j, b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
  have e : ∀ i j, b.repr ((b.repr u i • b i) * (b.repr v j • b j)) k
      = b.repr u i * b.repr v j * algebraMap ℚ R (ω.repr (ω i * ω j) k) := by
    intro i j
    rw [smul_mul_smul_comm, map_smul, Finsupp.smul_apply, smul_eq_mul, hb i, hb j, ← map_mul,
      repr_algebraMap_of_basis_eq ω b hb]
  conv_lhs => rw [← b.sum_repr u, ← b.sum_repr v]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply, e]
  exact Finset.sum_comm

/- English proof (translation)
Introduce `F β _ _ _ _ ω τ P`. Proceed by induction on `P using MvPolynomial.induction_on with`. Consider the case `C a`. Use `⟨fun k => MvPolynomial.C (ω.repr a k), ?_⟩` and prove the remaining obligations. Introduce `R A _ _ _ _ _ b hb x k`.

Rewrite using `[MvPolynomial.aeval_C, MvPolynomial.aeval_C, repr_algebraMap_of_basis_eq ω b hb]`. Consider the case `add p q hp hq`. Take `⟨Q1, h1⟩` from `hp`. Take `⟨Q2, h2⟩` from `hq`. Use `⟨fun k => Q1 k + Q2 k, ?_⟩` and prove the remaining obligations.

Introduce `R A _ _ _ _ _ b hb x k`. Rewrite using `[map_add, map_add, Finsupp.add_apply, map_add, h1 R A b hb x k, h2 R A b hb x k]`. Consider the case `mul_X p n hp`. Take `⟨Q1, h1⟩` from `hp`. Use `⟨fun k => ∑ i, ∑ j, Q1 i * MvPolynomial.X (n, j) * MvPolynomial.C (ω.repr (ω i * ω j) k), ?_⟩` and prove the remaining obligations.

Introduce `R A _ _ _ _ _ b hb x k`. Rewrite using `[map_mul, MvPolynomial.aeval_X, basis_repr_mul_of_basis_eq_algebraMap ω b hb]`. Simplify using `only [map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, h1 R A b hb x]`.
-/
theorem exists_coord_polynomial : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (τ : Type) (P : MvPolynomial τ F), ∃ Q : β → MvPolynomial (τ × β) ℚ, ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ (x : τ → A) (k : β), b.repr (MvPolynomial.aeval x P) k = MvPolynomial.aeval (fun p : τ × β => b.repr (x p.1) p.2) (Q k) := by
  intro F β _ _ _ _ ω τ P
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨fun k => MvPolynomial.C (ω.repr a k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_C, repr_algebraMap_of_basis_eq ω b hb]
  | add p q hp hq =>
    obtain ⟨Q1, h1⟩ := hp
    obtain ⟨Q2, h2⟩ := hq
    refine ⟨fun k => Q1 k + Q2 k, ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_add, map_add, Finsupp.add_apply, map_add, h1 R A b hb x k, h2 R A b hb x k]
  | mul_X p n hp =>
    obtain ⟨Q1, h1⟩ := hp
    refine ⟨fun k => ∑ i, ∑ j, Q1 i * MvPolynomial.X (n, j) *
      MvPolynomial.C (ω.repr (ω i * ω j) k), ?_⟩
    intro R A _ _ _ _ _ b hb x k
    rw [map_mul, MvPolynomial.aeval_X, basis_repr_mul_of_basis_eq_algebraMap ω b hb]
    simp only [map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, h1 R A b hb x]

end GlobalTheory.ClassFin
