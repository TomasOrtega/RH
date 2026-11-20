import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.OfDetToDet
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DAmitsur
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.DPoly

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
Rewrite using `[MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, Finsupp.tail_apply, MvPolynomial.algebraMap_eq]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem aeval_cons_monomial {A : Type} [CommRing A] {k : ℕ} (c : MvPolynomial (Fin k) A)
    (β : Fin (k + 1) →₀ ℕ) (a : A) :
    MvPolynomial.aeval (Fin.cons c MvPolynomial.X : Fin (k + 1) → MvPolynomial (Fin k) A)
      (MvPolynomial.monomial β a) = c ^ β 0 * MvPolynomial.monomial β.tail a := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ,
    MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fin.cons_zero, Fin.cons_succ, Finsupp.tail_apply, MvPolynomial.algebraMap_eq]
  ring

/- English proof (translation)
Rewrite using `[P.as_sum]`. Simplify using `only [map_sum, MvPolynomial.coeff_sum, aeval_cons_monomial]`. Use `Finset.sum_congr rfl fun β hβ => ?_` and prove the remaining obligations. Establish `hd : β.degree = n`. Assume the negation of the conclusion as `h`.

Conclude with `(MvPolynomial.mem_support_iff.1 hβ) (hP.coeff_eq_zero h)`. Distinguish the cases in `h0 : β 0 = 0`. Simplify using `[h0]`. Establish `hne : β.tail ≠ α`. Introduce and unpack `rfl`.

Rewrite `hd`, `hα` using `[Finsupp.degree_eq_sum]`. Rewrite `hd` using `[Fin.sum_univ_succ]`. Simplify using `only [Finsupp.tail_apply] at hα`. Use linear arithmetic over natural numbers and integers. Simplify using `[h0, MvPolynomial.coeff_monomial, hne]`.
-/
private theorem coeff_cons_eq {A : Type} [CommRing A] {k n : ℕ} (P : MvPolynomial (Fin (k + 1)) A)
    (hP : P.IsHomogeneous n) (α : Fin k →₀ ℕ) (hα : α.degree = n) :
    MvPolynomial.coeff α (MvPolynomial.aeval (Fin.cons 0 MvPolynomial.X : Fin (k + 1) → MvPolynomial (Fin k) A) P) =
    MvPolynomial.coeff α (MvPolynomial.aeval (Fin.cons 1 MvPolynomial.X : Fin (k + 1) → MvPolynomial (Fin k) A) P) := by
  classical
  rw [P.as_sum]
  simp only [map_sum, MvPolynomial.coeff_sum, aeval_cons_monomial]
  refine Finset.sum_congr rfl fun β hβ => ?_
  have hd : β.degree = n := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.1 hβ) (hP.coeff_eq_zero h)
  by_cases h0 : β 0 = 0
  · simp [h0]
  · have hne : β.tail ≠ α := by
      rintro rfl
      rw [Finsupp.degree_eq_sum] at hd hα
      rw [Fin.sum_univ_succ] at hd
      simp only [Finsupp.tail_apply] at hα
      omega
    simp [h0, MvPolynomial.coeff_monomial, hne]

/- English proof (translation)
Distinguish the cases in `hα : α.degree = n`. Use `swap`. Rewrite using `[(d_poly D x).1.coeff_eq_zero hα]`. Conclude with `A₀.zero_mem`. Take `⟨hh, hev⟩` from `d_poly D (Fin.cons 1 x : Fin (k + 1) → E)`.

Establish `h0` using `hev (MvPolynomial (Fin k) A) (Fin.cons 0 MvPolynomial.X)`. Establish `h1` using `hev (MvPolynomial (Fin k) A) (Fin.cons 1 MvPolynomial.X)`. Rewrite `h0`, `h1` using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ, zero_tmul, zero_add] at h0 h1`. Take `⟨P, hv, -, hP⟩` from `d_amitsur n k α`.

Establish `e : MvPolynomial.coeff α (D.poly x) = MvPolynomial.coeff α (D.D (MvPolynomial (Fin k) A) (1 + Det.gen x))`. Unfold `Det.poly Det.gen`. Rewrite using `[Algebra.TensorProduct.one_def, h0, h1]`. Conclude with `coeff_cons_eq _ hh α hα`. Rewrite using `[e, hP D x, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]`.

Use `A₀.sum_mem fun d hd => A₀.mul_mem (by simp) (A₀.prod_mem fun v hvd => A₀.pow_mem ?_ _)` and prove the remaining obligations. Take `⟨h1, h2, -⟩` from `hv v ((MvPolynomial.mem_vars_iff_mem_support v).2 ⟨d, hd, hvd⟩)`. Use `h _ ?_ _ h1 h2` and prove the remaining obligations. Rewrite using `[FreeMonoid.lift_apply]`. Use `M.list_prod_mem fun y hy => ?_` and prove the remaining obligations.

Take `⟨a, -, rfl⟩` from `List.mem_map.1 hy`. Conclude with `hx a`.
-/
private theorem coef_mem_fin {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E)
    (M : Submonoid E) (A₀ : Subring A) (h : ∀ x ∈ M, ∀ i, 1 ≤ i → i ≤ n → D.lam i x ∈ A₀) {k : ℕ}
    (x : Fin k → E) (hx : ∀ a, x a ∈ M) (α : Fin k →₀ ℕ) : MvPolynomial.coeff α (D.poly x) ∈ A₀ := by
  classical
  by_cases hα : α.degree = n
  swap
  · rw [(d_poly D x).1.coeff_eq_zero hα]; exact A₀.zero_mem
  obtain ⟨hh, hev⟩ := d_poly D (Fin.cons 1 x : Fin (k + 1) → E)
  have h0 := hev (MvPolynomial (Fin k) A) (Fin.cons 0 MvPolynomial.X)
  have h1 := hev (MvPolynomial (Fin k) A) (Fin.cons 1 MvPolynomial.X)
  rw [Fin.sum_univ_succ] at h0 h1
  simp only [Fin.cons_zero, Fin.cons_succ, zero_tmul, zero_add] at h0 h1
  obtain ⟨P, hv, -, hP⟩ := d_amitsur n k α
  have e : MvPolynomial.coeff α (D.poly x) =
      MvPolynomial.coeff α (D.D (MvPolynomial (Fin k) A) (1 + Det.gen x)) := by
    unfold Det.poly Det.gen
    rw [Algebra.TensorProduct.one_def, h0, h1]
    exact coeff_cons_eq _ hh α hα
  rw [e, hP D x, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine A₀.sum_mem fun d hd => A₀.mul_mem (by simp) (A₀.prod_mem fun v hvd => A₀.pow_mem ?_ _)
  obtain ⟨h1, h2, -⟩ := hv v ((MvPolynomial.mem_vars_iff_mem_support v).2 ⟨d, hd, hvd⟩)
  refine h _ ?_ _ h1 h2
  rw [FreeMonoid.lift_apply]
  refine M.list_prod_mem fun y hy => ?_
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hy
  exact hx a

/- English proof (translation)
Introduce `n A E _ _ _ D M A₀ h ι _ x hx α`. Set `e` to `(Fintype.equivFin ι).symm`. Establish `h1` using `(d_poly D (x ∘ e)).2 (MvPolynomial ι A) (MvPolynomial.X ∘ e)`. Establish `h2 : D.poly x = MvPolynomial.rename e (D.poly (x ∘ e))`. Rewrite using `[MvPolynomial.rename_eq_aeval, ← h1]`.

Unfold `Det.poly Det.gen`. Use `congr 1`. Conclude with `(Equiv.sum_comp e fun a => (MvPolynomial.X a : MvPolynomial ι A) ⊗ₜ[A] x a).symm`. Establish `h3 : α = (α.mapDomain e.symm).mapDomain e`. Rewrite using `[← Finsupp.mapDomain_comp]`.

Simplify using the standard rewrite rules. Rewrite using `[h2, h3, MvPolynomial.coeff_rename_mapDomain _ e.injective]`. Conclude with `coef_mem_fin D M A₀ h _ (fun a => hx _) _`.
-/
theorem UpperTheory.V.CA.d_coef_mem :
    ∀ {n : ℕ} {A E : Type} [CommRing A] [Ring E] [Algebra A E] (D : Det n A E) (M : Submonoid E) (A₀ : Subring A), (∀ x ∈ M, ∀ i, 1 ≤ i → i ≤ n → D.lam i x ∈ A₀) → ∀ {ι : Type} [Fintype ι] (x : ι → E), (∀ a, x a ∈ M) → ∀ α, MvPolynomial.coeff α (D.poly x) ∈ A₀ := by
  intro n A E _ _ _ D M A₀ h ι _ x hx α
  let e := (Fintype.equivFin ι).symm
  have h1 := (d_poly D (x ∘ e)).2 (MvPolynomial ι A) (MvPolynomial.X ∘ e)
  have h2 : D.poly x = MvPolynomial.rename e (D.poly (x ∘ e)) := by
    rw [MvPolynomial.rename_eq_aeval, ← h1]
    unfold Det.poly Det.gen
    congr 1
    exact (Equiv.sum_comp e fun a => (MvPolynomial.X a : MvPolynomial ι A) ⊗ₜ[A] x a).symm
  have h3 : α = (α.mapDomain e.symm).mapDomain e := by
    rw [← Finsupp.mapDomain_comp]; simp
  rw [h2, h3, MvPolynomial.coeff_rename_mapDomain _ e.injective]
  exact coef_mem_fin D M A₀ h _ (fun a => hx _) _
