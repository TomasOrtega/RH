import Mathlib
import Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsPolynomialEqMapEvalRootsOfPermInvariant

noncomputable section
open Polynomial

/- English proof (translation)
Rewrite using `[Polynomial.map_prod]`. Establish `hterm : ∀ J : Finset (Fin N), ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i)).map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom = X - C (∏ i ∈ J.map σ.toEmbedding, MvPolynomial.X i)`. Introduce `J`. Rewrite using `[Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Finset.prod_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod]`. Simplify using `only [MvPolynomial.rename_X, Equiv.coe_toEmbedding]`.

Rewrite using `[Finset.prod_congr rfl (fun J _ => hterm J)]`. Use `Finset.prod_nbij' (fun J => J.map σ.toEmbedding) (fun J => J.map σ.symm.toEmbedding) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `J hJ`. Rewrite `hJ`, the goal using `[Finset.mem_powersetCard]`. Conclude with `⟨Finset.subset_univ _, by rw [Finset.card_map, hJ.2]⟩`.

Introduce `J hJ`. Rewrite `hJ`, the goal using `[Finset.mem_powersetCard]`. Conclude with `⟨Finset.subset_univ _, by rw [Finset.card_map, hJ.2]⟩`. Introduce `J _`. Simplify using `[Finset.map_map]`.

Introduce `J _`. Simplify using `[Finset.map_map]`. Introduce `J _`. Both sides reduce to the same expression.
-/
private lemma Phi_sym {A : Type} [CommRing A] (N m : ℕ) (σ : Equiv.Perm (Fin N)) :
    (∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
      ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i))).map
      (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom =
    ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
      ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i)) := by
  rw [Polynomial.map_prod]
  have hterm : ∀ J : Finset (Fin N),
      ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i)).map
        (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom =
      X - C (∏ i ∈ J.map σ.toEmbedding, MvPolynomial.X i) := by
    intro J
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Finset.prod_map,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod]
    simp only [MvPolynomial.rename_X, Equiv.coe_toEmbedding]
  rw [Finset.prod_congr rfl (fun J _ => hterm J)]
  refine Finset.prod_nbij' (fun J => J.map σ.toEmbedding) (fun J => J.map σ.symm.toEmbedding)
    ?_ ?_ ?_ ?_ ?_
  · intro J hJ
    rw [Finset.mem_powersetCard] at hJ ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map, hJ.2]⟩
  · intro J hJ
    rw [Finset.mem_powersetCard] at hJ ⊢
    exact ⟨Finset.subset_univ _, by rw [Finset.card_map, hJ.2]⟩
  · intro J _
    simp [Finset.map_map]
  · intro J _
    simp [Finset.map_map]
  · intro J _
    rfl

/- English proof (translation)
Rewrite using `[derivative_prod_finset]`. Simplify using `[eval_finset_sum, eval_prod]`.
-/
private lemma eval_derivative_prod_X_sub_C {R ι : Type*} [CommRing R] [DecidableEq ι] (s : Finset ι) (y : ι → R) (a : R) :
    (derivative (∏ J ∈ s, ((X : R[X]) - C (y J)))).eval a = ∑ J ∈ s, ∏ J' ∈ s.erase J, (a - y J') := by
  rw [derivative_prod_finset]
  simp [eval_finset_sum, eval_prod]

/- English proof (translation)
Use `set Φ : (MvPolynomial (Fin N) A)[X] := ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i)) with hΦ`. Use `set d := Nat.choose N m with hd`. Establish `hdpos : 0 < d` using `Nat.choose_pos hm`. Establish `hΦm : Φ.Monic` using `Polynomial.monic_prod_of_monic _ _ (fun J _ => Polynomial.monic_X_sub_C _)`. Establish `hΦdeg : Φ.natDegree = d`.

Rewrite using `[hΦ, Polynomial.natDegree_prod_of_monic _ _ (fun J _ => Polynomial.monic_X_sub_C _), Finset.sum_congr rfl (fun J _ => Polynomial.natDegree_X_sub_C _)]`. Simplify using `[Finset.card_powersetCard, hd]`. Establish `hsym : ∀ σ : Equiv.Perm (Fin N), (Φ - X ^ d).map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom = Φ - X ^ d`. Introduce `σ`. Rewrite using `[Polynomial.map_sub, hΦ, Phi_sym, Polynomial.map_pow, Polynomial.map_X]`.

Take `⟨p, hpdeg, hp⟩` from `UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant A N g (Φ - X ^ d) hsym`. Establish `hlt : (Φ - X ^ d).natDegree < d`. Distinguish the cases in `h0 : Φ - X ^ d = 0`. Rewrite using `[h0, Polynomial.natDegree_zero]`. Conclude with `hdpos`.

Rewrite using `[Polynomial.natDegree_lt_iff_degree_lt h0]`. Establish `hdeg : Φ.degree = (X ^ d : (MvPolynomial (Fin N) A)[X]).degree`. Rewrite using `[Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hΦm.ne_zero, hΦdeg]`. Use `Polynomial.degree_sub_lt hdeg hΦm.ne_zero (by rw [hΦm.leadingCoeff, Polynomial.leadingCoeff_X_pow])` as an intermediate fact. Rewrite `this` using `[Polynomial.degree_eq_natDegree hΦm.ne_zero, hΦdeg]`. Then use the resulting hypothesis.

Use `⟨X ^ d + p, ?_, ?_⟩` and prove the remaining obligations. Apply `Polynomial.Monic.add_of_left (Polynomial.monic_X_pow d)` to reduce the goal to its premises. Rewrite using `[Polynomial.degree_X_pow]`. Conclude with `lt_of_le_of_lt Polynomial.degree_le_natDegree (by exact_mod_cast lt_of_le_of_lt hpdeg hlt)`. Introduce `S _ _ x hx`.

Rewrite using `[Polynomial.map_add, hp S x hx, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, add_sub_cancel, hΦ, Polynomial.map_prod]`. Use `Finset.prod_congr rfl (fun J _ => ?_)` and prove the remaining obligations. Rewrite using `[Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_prod]`. Simplify using `only [MvPolynomial.aeval_X]`.
-/
private lemma exists_chi {A : Type} [CommRing A] [Nontrivial A] (g : A[X]) (N m : ℕ) (hm : m ≤ N) :
    ∃ χ : A[X], χ.Monic ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S),
      g.map (algebraMap A S) = ∏ i, (X - C (x i)) →
      χ.map (algebraMap A S) =
        ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (X - C (∏ i ∈ J, x i)) := by
  classical
  set Φ : (MvPolynomial (Fin N) A)[X] := ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)),
      ((X : (MvPolynomial (Fin N) A)[X]) - C (∏ i ∈ J, MvPolynomial.X i)) with hΦ
  set d := Nat.choose N m with hd
  have hdpos : 0 < d := Nat.choose_pos hm
  have hΦm : Φ.Monic := Polynomial.monic_prod_of_monic _ _ (fun J _ => Polynomial.monic_X_sub_C _)
  have hΦdeg : Φ.natDegree = d := by
    rw [hΦ, Polynomial.natDegree_prod_of_monic _ _ (fun J _ => Polynomial.monic_X_sub_C _),
      Finset.sum_congr rfl (fun J _ => Polynomial.natDegree_X_sub_C _)]
    simp [Finset.card_powersetCard, hd]
  have hsym : ∀ σ : Equiv.Perm (Fin N),
      (Φ - X ^ d).map (MvPolynomial.rename σ : MvPolynomial (Fin N) A →ₐ[A] _).toRingHom = Φ - X ^ d := by
    intro σ
    rw [Polynomial.map_sub, hΦ, Phi_sym, Polynomial.map_pow, Polynomial.map_X]
  obtain ⟨p, hpdeg, hp⟩ := UpperTheory.exists_polynomial_eq_map_eval_roots_of_perm_invariant A N g (Φ - X ^ d) hsym
  have hlt : (Φ - X ^ d).natDegree < d := by
    by_cases h0 : Φ - X ^ d = 0
    · rw [h0, Polynomial.natDegree_zero]; exact hdpos
    · rw [Polynomial.natDegree_lt_iff_degree_lt h0]
      have hdeg : Φ.degree = (X ^ d : (MvPolynomial (Fin N) A)[X]).degree := by
        rw [Polynomial.degree_X_pow, Polynomial.degree_eq_natDegree hΦm.ne_zero, hΦdeg]
      have := Polynomial.degree_sub_lt hdeg hΦm.ne_zero
        (by rw [hΦm.leadingCoeff, Polynomial.leadingCoeff_X_pow])
      rwa [Polynomial.degree_eq_natDegree hΦm.ne_zero, hΦdeg] at this
  refine ⟨X ^ d + p, ?_, ?_⟩
  · apply Polynomial.Monic.add_of_left (Polynomial.monic_X_pow d)
    rw [Polynomial.degree_X_pow]
    exact lt_of_le_of_lt Polynomial.degree_le_natDegree
      (by exact_mod_cast lt_of_le_of_lt hpdeg hlt)
  · intro S _ _ x hx
    rw [Polynomial.map_add, hp S x hx, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_sub,
      Polynomial.map_pow, Polynomial.map_X, add_sub_cancel, hΦ, Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun J _ => ?_)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, map_prod]
    simp only [MvPolynomial.aeval_X]

/- English proof (translation)
Introduce `A _ I _ g n m N hnm hg hdeg hmod`. Substitute `hnm` using the available equality. Break down `subsingleton_or_nontrivial A with hA | hA` into its components or cases. Use `⟨1, 1, by rw [Subsingleton.elim (1 - 1 : A) 0]; exact I.zero_mem, ?_⟩` and prove the remaining obligations. Introduce `S _ _ x _`.

Establish `h10 : (1 : S) = 0`. Rewrite using `[← map_one (algebraMap A S), Subsingleton.elim (1 : A) 0, map_zero]`. Use `haveI : Subsingleton S := subsingleton_of_zero_eq_one h10.symm`. Conclude with `⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩`. Take `⟨χ, hχm, hχ⟩` from `exists_chi g (n + m) m (Nat.le_add_left m n)`.

Set `x0 : Fin (n + m) → A ⧸ I` to `fun i => if (i : ℕ) < m then 1 else 0`. Establish `hprod : ∏ i : Fin (n + m), ((X : (A ⧸ I)[X]) - C (x0 i)) = X ^ n * (X - 1) ^ m`. Establish `h` using `Fin.prod_univ_eq_prod_range (fun k => (X : (A ⧸ I)[X]) - C (if k < m then 1 else 0)) (n + m)`. Rewrite using `[h, show n + m = m + n from add_comm n m, Finset.prod_range_add]`. Establish `h1 : ∏ k ∈ Finset.range m, ((X : (A ⧸ I)[X]) - C (if k < m then 1 else 0)) = (X - 1) ^ m`.

Rewrite using `[Finset.prod_congr rfl (fun k hk => by rw [if_pos (Finset.mem_range.mp hk), map_one])]`. Simplify using the standard rewrite rules. Establish `h2 : ∏ k ∈ Finset.range n, ((X : (A ⧸ I)[X]) - C (if m + k < m then 1 else 0)) = X ^ n`. Rewrite using `[Finset.prod_congr rfl (fun k _ => by rw [if_neg (by omega), map_zero, sub_zero])]`. Simplify using the standard rewrite rules.

Rewrite using `[h1, h2, mul_comm]`. Establish `hsplit : g.map (algebraMap A (A ⧸ I)) = ∏ i, (X - C (x0 i))`. Rewrite using `[Ideal.Quotient.algebraMap_eq, hmod, hprod]`. Establish `hS` using `hχ (A ⧸ I) x0 hsplit`. Set `T : Finset (Fin (n + m))` to `Finset.univ.filter (fun i => (i : ℕ) < m)`.

Establish `hT : T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin (n + m)))`. Rewrite using `[Finset.mem_powersetCard]`. Use `⟨Finset.subset_univ _, ?_⟩` and prove the remaining obligations. Simplify using `only [T, Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers.

Establish `hyT : ∏ i ∈ T, x0 i = 1` using `Finset.prod_eq_one (fun i hi => by simp [x0, (Finset.mem_filter.mp hi).2])`. Establish `hyJ : ∀ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin (n + m))), J ≠ T → ∏ i ∈ J, x0 i = 0`. Introduce `J hJ hne`. Assume the negation of the conclusion as `h`. Apply `hne` to reduce the goal to its premises.

Establish `hsub : J ⊆ T`. Introduce `i hi`. Rewrite using `[Finset.mem_filter]`. Use `⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`.

Conclude with `h (Finset.prod_eq_zero hi (by simp [x0, hlt]))`. Conclude with `Finset.eq_of_subset_of_card_le hsub (by rw [(Finset.mem_powersetCard.mp hJ).2, (Finset.mem_powersetCard.mp hT).2])`. Establish `hev : ∀ q : A[X], (q.map (algebraMap A (A ⧸ I))).eval 1 = Ideal.Quotient.mk I (q.eval 1)`. Introduce `q`. Rewrite using `[Polynomial.eval_map, ← map_one (algebraMap A (A ⧸ I)), Polynomial.eval₂_at_apply]`.

Both sides reduce to the same expression. Establish `hE0 : Ideal.Quotient.mk I (χ.eval 1) = 0`. Rewrite using `[← hev, hS]`. Simplify using `only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]`. Conclude with `Finset.prod_eq_zero hT (by rw [hyT, sub_self])`.

Establish `hE1 : Ideal.Quotient.mk I ((derivative χ).eval 1) = 1`. Rewrite using `[← hev, ← Polynomial.derivative_map, hS]`. Establish `hd` using `eval_derivative_prod_X_sub_C (Finset.powersetCard m (Finset.univ : Finset (Fin (n + m)))) (fun J => ∏ i ∈ J, x0 i) (1 : A ⧸ I)`. Rewrite using `[hd, Finset.sum_eq_single T]`. Conclude with `Finset.prod_eq_one (fun J hJ => by`.

Rewrite using `[hyJ J (Finset.mem_of_mem_erase hJ) (Finset.ne_of_mem_erase hJ), sub_zero])`. Introduce `J _ hne`. Conclude with `Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hT⟩) (by rw [hyT, sub_self])`. Introduce `h`. Conclude with `absurd hT h`.

Establish `hmem : χ.eval 1 ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hE0`. Establish `hu1 : IsUnit (Ideal.Quotient.mk I ((derivative χ).eval 1))`. Rewrite using `[hE1]`.

Conclude with `isUnit_one`. Take `⟨α, hαroot, hα1⟩` from `HenselianRing.is_henselian (R := A) (I := I) χ hχm 1 hmem hu1`. Establish `hcong : Ideal.Quotient.mk I ((derivative χ).eval α) = Ideal.Quotient.mk I ((derivative χ).eval 1)`. Rewrite using `[Ideal.Quotient.eq]`. Take `⟨k, hk⟩` from `Polynomial.sub_dvd_eval_sub α 1 (derivative χ)`.

Rewrite using `[hk]`. Conclude with `I.mul_mem_right k hα1`. Establish `hunit : IsUnit ((derivative χ).eval α)` using `by haveI := isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (I := I))`. Conclude with `isUnit_of_map_unit (Ideal.Quotient.mk I) _ (by rw [hcong, hE1]; exact isUnit_one)`. Use `⟨α, hunit.unit, hα1, ?_⟩` and prove the remaining obligations.

Introduce `S _ _ x hx`. Establish `hSx` using `hχ S x hx`. Prove the components needed by the constructor for the conclusion. Establish `h` using `congrArg (fun q => q.eval (algebraMap A S α)) hSx`. Simplify using `only [Polynomial.eval_map, Polynomial.eval₂_at_apply, hαroot.eq_zero, map_zero, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h`.

Conclude with `h.symm`. Establish `h` using `congrArg (fun q => (derivative q).eval (algebraMap A S α)) hSx`. Establish `hd` using `eval_derivative_prod_X_sub_C (Finset.powersetCard m (Finset.univ : Finset (Fin (n + m)))) (fun J => ∏ i ∈ J, x i) (algebraMap A S α)`. Simplify using `only [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply] at h`. Rewrite `h` using `[hd]`.

Rewrite using `[hunit.unit_spec]`. Conclude with `h.symm`.
-/
theorem UpperTheory.exists_root_subset_product_equation_of_henselian_reduction :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (g : A[X]) (n m N : ℕ), n + m = N → g.Monic → g.natDegree = N → g.map (Ideal.Quotient.mk I) = X ^ n * (X - 1) ^ m →
      ∃ (α : A) (c : Aˣ), α - 1 ∈ I ∧ ∀ (S : Type) [CommRing S] [Algebra A S] (x : Fin N → S), g.map (algebraMap A S) = ∏ i, (X - C (x i)) →
        ∏ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), (algebraMap A S α - ∏ i ∈ J, x i) = 0 ∧
        ∑ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin N)), ∏ J' ∈ (Finset.powersetCard m (Finset.univ : Finset (Fin N))).erase J, (algebraMap A S α - ∏ i ∈ J', x i) = algebraMap A S c := by
  intro A _ I _ g n m N hnm hg hdeg hmod
  classical
  subst hnm
  rcases subsingleton_or_nontrivial A with hA | hA
  · refine ⟨1, 1, by rw [Subsingleton.elim (1 - 1 : A) 0]; exact I.zero_mem, ?_⟩
    intro S _ _ x _
    have h10 : (1 : S) = 0 := by
      rw [← map_one (algebraMap A S), Subsingleton.elim (1 : A) 0, map_zero]
    haveI : Subsingleton S := subsingleton_of_zero_eq_one h10.symm
    exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  · obtain ⟨χ, hχm, hχ⟩ := exists_chi g (n + m) m (Nat.le_add_left m n)
    let x0 : Fin (n + m) → A ⧸ I := fun i => if (i : ℕ) < m then 1 else 0
    have hprod : ∏ i : Fin (n + m), ((X : (A ⧸ I)[X]) - C (x0 i)) = X ^ n * (X - 1) ^ m := by
      have h := Fin.prod_univ_eq_prod_range
        (fun k => (X : (A ⧸ I)[X]) - C (if k < m then 1 else 0)) (n + m)
      rw [h, show n + m = m + n from add_comm n m, Finset.prod_range_add]
      have h1 : ∏ k ∈ Finset.range m, ((X : (A ⧸ I)[X]) - C (if k < m then 1 else 0)) =
          (X - 1) ^ m := by
        rw [Finset.prod_congr rfl (fun k hk => by rw [if_pos (Finset.mem_range.mp hk), map_one])]
        simp
      have h2 : ∏ k ∈ Finset.range n, ((X : (A ⧸ I)[X]) - C (if m + k < m then 1 else 0)) =
          X ^ n := by
        rw [Finset.prod_congr rfl (fun k _ => by rw [if_neg (by omega), map_zero, sub_zero])]
        simp
      rw [h1, h2, mul_comm]
    have hsplit : g.map (algebraMap A (A ⧸ I)) = ∏ i, (X - C (x0 i)) := by
      rw [Ideal.Quotient.algebraMap_eq, hmod, hprod]
    have hS := hχ (A ⧸ I) x0 hsplit
    let T : Finset (Fin (n + m)) := Finset.univ.filter (fun i => (i : ℕ) < m)
    have hT : T ∈ Finset.powersetCard m (Finset.univ : Finset (Fin (n + m))) := by
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      simp only [T, Fin.card_filter_val_lt]
      omega
    have hyT : ∏ i ∈ T, x0 i = 1 :=
      Finset.prod_eq_one (fun i hi => by simp [x0, (Finset.mem_filter.mp hi).2])
    have hyJ : ∀ J ∈ Finset.powersetCard m (Finset.univ : Finset (Fin (n + m))), J ≠ T →
        ∏ i ∈ J, x0 i = 0 := by
      intro J hJ hne
      by_contra h
      apply hne
      have hsub : J ⊆ T := by
        intro i hi
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        by_contra hlt
        exact h (Finset.prod_eq_zero hi (by simp [x0, hlt]))
      exact Finset.eq_of_subset_of_card_le hsub
        (by rw [(Finset.mem_powersetCard.mp hJ).2, (Finset.mem_powersetCard.mp hT).2])
    have hev : ∀ q : A[X], (q.map (algebraMap A (A ⧸ I))).eval 1 = Ideal.Quotient.mk I (q.eval 1) := by
      intro q
      rw [Polynomial.eval_map, ← map_one (algebraMap A (A ⧸ I)), Polynomial.eval₂_at_apply]
      rfl
    have hE0 : Ideal.Quotient.mk I (χ.eval 1) = 0 := by
      rw [← hev, hS]
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      exact Finset.prod_eq_zero hT (by rw [hyT, sub_self])
    have hE1 : Ideal.Quotient.mk I ((derivative χ).eval 1) = 1 := by
      rw [← hev, ← Polynomial.derivative_map, hS]
      have hd := eval_derivative_prod_X_sub_C (Finset.powersetCard m (Finset.univ : Finset (Fin (n + m))))
        (fun J => ∏ i ∈ J, x0 i) (1 : A ⧸ I)
      rw [hd, Finset.sum_eq_single T]
      · exact Finset.prod_eq_one (fun J hJ => by
          rw [hyJ J (Finset.mem_of_mem_erase hJ) (Finset.ne_of_mem_erase hJ), sub_zero])
      · intro J _ hne
        exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨fun h => hne h.symm, hT⟩)
          (by rw [hyT, sub_self])
      · intro h
        exact absurd hT h
    have hmem : χ.eval 1 ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact hE0
    have hu1 : IsUnit (Ideal.Quotient.mk I ((derivative χ).eval 1)) := by
      rw [hE1]
      exact isUnit_one
    obtain ⟨α, hαroot, hα1⟩ := HenselianRing.is_henselian (R := A) (I := I) χ hχm 1 hmem hu1
    have hcong : Ideal.Quotient.mk I ((derivative χ).eval α) =
        Ideal.Quotient.mk I ((derivative χ).eval 1) := by
      rw [Ideal.Quotient.eq]
      obtain ⟨k, hk⟩ := Polynomial.sub_dvd_eval_sub α 1 (derivative χ)
      rw [hk]
      exact I.mul_mem_right k hα1
    have hunit : IsUnit ((derivative χ).eval α) := by
      haveI := isLocalHom_of_le_jacobson_bot I (HenselianRing.jac (I := I))
      exact isUnit_of_map_unit (Ideal.Quotient.mk I) _ (by rw [hcong, hE1]; exact isUnit_one)
    refine ⟨α, hunit.unit, hα1, ?_⟩
    intro S _ _ x hx
    have hSx := hχ S x hx
    constructor
    · have h := congrArg (fun q => q.eval (algebraMap A S α)) hSx
      simp only [Polynomial.eval_map, Polynomial.eval₂_at_apply, hαroot.eq_zero, map_zero,
        Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h
      exact h.symm
    · have h := congrArg (fun q => (derivative q).eval (algebraMap A S α)) hSx
      have hd := eval_derivative_prod_X_sub_C (Finset.powersetCard m (Finset.univ : Finset (Fin (n + m))))
        (fun J => ∏ i ∈ J, x i) (algebraMap A S α)
      simp only [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply] at h
      rw [hd] at h
      rw [hunit.unit_spec]
      exact h.symm

end
