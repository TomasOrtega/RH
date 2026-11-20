import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Rewrite using `[MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]`. Simplify using `only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod, map_pow, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]`. Rewrite using `[show Finsupp.degree d = ∑ i ∈ d.support, d i from rfl]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem aeval_X_mul_C_X_monomial {A ι : Type} [CommRing A] (d : ι →₀ ℕ) (c : A) :
    MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) (MvPolynomial.monomial d c) =
      X ^ (Finsupp.degree d) * C (MvPolynomial.monomial d c) := by
  rw [MvPolynomial.aeval_monomial, MvPolynomial.monomial_eq]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, map_mul, map_prod,
    map_pow, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rw [show Finsupp.degree d = ∑ i ∈ d.support, d i from rfl]
  ring

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on' with`. Consider the case `monomial d c`. Rewrite using `[aeval_X_mul_C_X_monomial, Polynomial.coeff_X_pow_mul', MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl), Polynomial.coeff_C]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`. Consider the case `add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, map_add]`.
-/
private theorem scale_coeff {A ι : Type} [CommRing A] (P : MvPolynomial ι A) (k : ℕ) :
    (MvPolynomial.aeval (fun a => (X * C (MvPolynomial.X a) : (MvPolynomial ι A)[X])) P).coeff k =
      MvPolynomial.homogeneousComponent k P := by
  induction P using MvPolynomial.induction_on' with
  | monomial d c =>
    rw [aeval_X_mul_C_X_monomial, Polynomial.coeff_X_pow_mul',
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl), Polynomial.coeff_C]
    split_ifs <;> first | rfl | omega
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, hp, hq, map_add]

/- English proof (translation)
Introduce `n A E _ _ _ D ι _ x`. Establish `key : ∀ (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S), D.D S (∑ a, f (MvPolynomial.X a) ⊗ₜ x a) = f (D.poly x)`. Introduce `S _ _ f`. Rewrite using `[Det.poly, ← D.nat]`. Use `congr 1`.

Simplify using `[Det.gen, map_sum]`. Use `⟨?_, fun S _ _ s => by simpa using key S (MvPolynomial.aeval s)⟩` and prove the remaining obligations. Set `g : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X]` to `MvPolynomial.aeval fun a => X * C (MvPolynomial.X a)`. Set `t : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X]` to `IsScalarTower.toAlgHom A (MvPolynomial ι A) (MvPolynomial ι A)[X]`. Establish `h1` using `key _ g`.

Establish `h3` using `key _ t`. Establish `h2 : (∑ a, g (MvPolynomial.X a) ⊗ₜ[A] x a) = (X : (MvPolynomial ι A)[X]) • ∑ a, t (MvPolynomial.X a) ⊗ₜ[A] x a`. Rewrite using `[Finset.smul_sum]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.smul_tmul', smul_eq_mul]`.

Simplify using `[g, t]`. Rewrite `h1` using `[h2, D.homog, h3]`. Establish `hc` using `congrArg (fun p : (MvPolynomial ι A)[X] => p.coeff n) h1`. Simplify using `only [g, t, scale_coeff, IsScalarTower.coe_toAlgHom', Polynomial.coeff_X_pow_mul', le_refl, if_true, Nat.sub_self] at hc`. Establish `hP : MvPolynomial.homogeneousComponent n (D.poly x) = D.poly x`.

Rewrite using `[← hc]`. Simplify using the standard rewrite rules. Conclude with `hP ▸ MvPolynomial.homogeneousComponent_isHomogeneous n _`.
-/
theorem UpperTheory.V.CA.d_poly :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) {ι : Type} [Fintype ι] (x : ι → E), (D.poly x).IsHomogeneous n ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (s : ι → S), D.D S (∑ a, s a ⊗ₜ x a) = MvPolynomial.aeval s (D.poly x) := by
  intro n A E _ _ _ D ι _ x
  have key : ∀ (S : Type) [CommRing S] [Algebra A S] (f : MvPolynomial ι A →ₐ[A] S),
      D.D S (∑ a, f (MvPolynomial.X a) ⊗ₜ x a) = f (D.poly x) := by
    intro S _ _ f
    rw [Det.poly, ← D.nat]
    congr 1
    simp [Det.gen, map_sum]
  refine ⟨?_, fun S _ _ s => by simpa using key S (MvPolynomial.aeval s)⟩
  let g : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := MvPolynomial.aeval fun a => X * C (MvPolynomial.X a)
  let t : MvPolynomial ι A →ₐ[A] (MvPolynomial ι A)[X] := IsScalarTower.toAlgHom A (MvPolynomial ι A) (MvPolynomial ι A)[X]
  have h1 := key _ g
  have h3 := key _ t
  have h2 : (∑ a, g (MvPolynomial.X a) ⊗ₜ[A] x a) = (X : (MvPolynomial ι A)[X]) • ∑ a, t (MvPolynomial.X a) ⊗ₜ[A] x a := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [TensorProduct.smul_tmul', smul_eq_mul]
    simp [g, t]
  rw [h2, D.homog, h3] at h1
  have hc := congrArg (fun p : (MvPolynomial ι A)[X] => p.coeff n) h1
  simp only [g, t, scale_coeff, IsScalarTower.coe_toAlgHom', Polynomial.coeff_X_pow_mul', le_refl, if_true,
    Nat.sub_self] at hc
  have hP : MvPolynomial.homogeneousComponent n (D.poly x) = D.poly x := by
    rw [← hc]
    simp
  exact hP ▸ MvPolynomial.homogeneousComponent_isHomogeneous n _
