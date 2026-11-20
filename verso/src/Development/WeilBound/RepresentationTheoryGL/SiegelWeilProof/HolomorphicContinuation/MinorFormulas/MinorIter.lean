import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorCore

noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.SP.Mi

variable {R : Type} [CommRing R] {ρ : ℕ}

/- English proof (translation)
Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero]`.
-/
theorem del_C_mul (p q : Fin ρ) (r : R) (g : Pm R ρ) : del p q (C r * g) = C r * del p q g := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, MvPolynomial.derivation_C, mul_zero, add_zero]

/- English proof (translation)
Simplify using `only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, del_C_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem opE_C_mul' (α : R) (p q : Fin ρ) (r : R) (g : Pm R ρ) : opE α p q (C r * g) = C r * opE α p q g := by
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe, del_C_mul]
  ring

/- English proof (translation)
Rewrite using `[Derivation.leibniz_pow, delDet, smul_eq_mul, nsmul_eq_mul]`. Break down `k with _ | k` into its components or cases. Simplify using the standard rewrite rules. Rewrite using `[pow_succ]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem del_det_pow (p q : Fin ρ) (k : ℕ) :
    del p q ((Xm R ρ).det ^ k) = (k : Pm R ρ) * X (q, p) * (Xm R ρ).det ^ k := by
  rw [Derivation.leibniz_pow, delDet, smul_eq_mul, nsmul_eq_mul]
  rcases k with _ | k
  · simp
  · rw [pow_succ]
    push_cast
    ring

/- English proof (translation)
Simplify using `only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]`. Rewrite using `[Derivation.leibniz, smul_eq_mul, smul_eq_mul, del_det_pow]`. Simplify using `only [map_add, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem opE_det_pow_mul (α : R) (p q : Fin ρ) (k : ℕ) (g : Pm R ρ) :
    opE α p q ((Xm R ρ).det ^ k * g) = (Xm R ρ).det ^ k * opE (α + k) p q g := by
  simp only [opE, LinearMap.add_apply, LinearMap.mulLeft_apply, Derivation.coeFn_coe]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, del_det_pow]
  simp only [map_add, map_natCast]
  ring

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_det_pow_mul]`.
-/
theorem foldr_det_pow (α : R) (k : ℕ) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) ((Xm R ρ).det ^ k * g) =
      (Xm R ρ).det ^ k * (L.foldr (fun j h => opE (α + k) j (σ j) ∘ₗ h) LinearMap.id) g := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_det_pow_mul]

/- English proof (translation)
Simplify using `only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_det_pow, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm]`.
-/
theorem detE_det_pow_mul (α : R) (k : ℕ) (g : Pm R ρ) :
    detE α ((Xm R ρ).det ^ k * g) = (Xm R ρ).det ^ k * detE (α + k) g := by
  simp only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_det_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_C_mul']`.
-/
theorem foldr_C_mul (α : R) (r : R) (σ : Equiv.Perm (Fin ρ)) (L : List (Fin ρ)) (g : Pm R ρ) :
    (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) (C r * g) =
      C r * (L.foldr (fun j h => opE α j (σ j) ∘ₗ h) LinearMap.id) g := by
  induction L with
  | nil => simp
  | cons a L ih => simp only [List.foldr_cons, LinearMap.comp_apply, ih, opE_C_mul']

/- English proof (translation)
Simplify using `only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_C_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[mul_smul_comm]`.
-/
theorem detE_C_mul (α : R) (r : R) (g : Pm R ρ) : detE α (C r * g) = C r * detE α g := by
  simp only [detE, LinearMap.sum_apply, LinearMap.smul_apply, foldr_C_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [mul_smul_comm]

/- English proof (translation)
Introduce `R _ ρ α N`. Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ N ih`. Rewrite using `[Function.iterate_succ_apply', ih]`.

Establish `hc : (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (C α + (l : Pm R ρ) - (i : Pm R ρ))) = C (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R)))`. Simplify using `[map_prod]`. Use `set r := ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R))`. Establish `h1 : (C r : Pm R ρ) = C r * 1` using `(mul_one _).symm`. Rewrite using `[hc, mul_comm, detE_det_pow_mul, h1, detE_C_mul, core]`.

Rewrite using `[Finset.prod_range_succ, hc]`. Simplify using `only [map_prod, map_sub, map_add, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem iter : Iter := by
  intro R _ ρ α N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Function.iterate_succ_apply', ih]
    have hc : (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (C α + (l : Pm R ρ) - (i : Pm R ρ))) =
        C (∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R))) := by
      simp [map_prod]
    set r := ∏ l ∈ Finset.range N, ∏ i ∈ Finset.range ρ, (α + (l : R) - (i : R))
    have h1 : (C r : Pm R ρ) = C r * 1 := (mul_one _).symm
    rw [hc, mul_comm, detE_det_pow_mul, h1, detE_C_mul, core]
    rw [Finset.prod_range_succ, hc]
    simp only [map_prod, map_sub, map_add, map_natCast]
    ring

end PositivityTheory.Rg.Sw.SP.Mi
