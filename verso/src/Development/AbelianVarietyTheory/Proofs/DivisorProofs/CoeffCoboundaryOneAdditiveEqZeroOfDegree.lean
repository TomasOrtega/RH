import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz

/- English proof (translation)
Introduce `γ h`. Rewrite `h` using `[coeff_one]`. Distinguish the cases in `h0 : γ = 0`. Simplify using `[h0]`. Simplify using `[h0] at h`.
-/
private theorem homog_one {R τ : Type} [CommRing R] : (1 : MvPowerSeries τ R).IsHomogeneous 0 := by
  classical
  intro γ h
  rw [coeff_one] at h
  by_cases h0 : γ = 0
  · simp [h0]
  · simp [h0] at h

/- English proof (translation)
Introduce `γ h`. Rewrite `h` using `[coeff_X]`. Distinguish the cases in `h0 : γ = Finsupp.single t 1`. Simplify using `[h0, Finsupp.weight_single]`. Simplify using `[h0] at h`.
-/
private theorem homog_X {R τ : Type} [CommRing R] (t : τ) :
    (X t : MvPowerSeries τ R).IsHomogeneous 1 := by
  classical
  intro γ h
  rw [coeff_X] at h
  by_cases h0 : γ = Finsupp.single t 1
  · simp [h0, Finsupp.weight_single]
  · simp [h0] at h

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `homog_one`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `IsHomogeneous.mul (f := f ^ n) (g := f) ih hf`.
-/
private theorem homog_pow {R τ : Type} [CommRing R] {f : MvPowerSeries τ R}
    (hf : f.IsHomogeneous 1) (n : ℕ) : (f ^ n).IsHomogeneous n := by
  induction n with
  | zero => rw [pow_zero]; exact homog_one
  | succ n ih => rw [pow_succ]; exact IsHomogeneous.mul (f := f ^ n) (g := f) ih hf

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.prod_empty, Finset.sum_empty]`. Conclude with `homog_one`. Consider the case `insert i s hi ih`. Rewrite using `[Finset.prod_insert hi, Finset.sum_insert hi]`.

Conclude with `IsHomogeneous.mul (f := a i ^ n i) (p := n i) (homog_pow (ha i) (n i)) ih`.
-/
private theorem homog_prod {R σ τ : Type} [CommRing R] {a : σ → MvPowerSeries τ R}
    (ha : ∀ i, (a i).IsHomogeneous 1) (n : σ → ℕ) (s : Finset σ) :
    (∏ i ∈ s, a i ^ n i).IsHomogeneous (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact homog_one
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]; exact IsHomogeneous.mul (f := a i ^ n i) (p := n i) (homog_pow (ha i) (n i)) ih

/- English proof (translation)
Establish `hs : HasSubst a` using `hasSubst_of_constantCoeff_zero fun i => by`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Conclude with `IsHomogeneous.coeff_eq_zero (f := a i) (p := 1) (ha i) (by simp)`. Rewrite using `[coeff_subst hs]`. Use `finsum_eq_zero_of_forall_eq_zero fun α => ?_` and prove the remaining obligations.

Distinguish the cases in `h : α.degree = N`. Rewrite using `[hb α h, zero_smul]`. Use `IsHomogeneous.coeff_eq_zero (f := ∏ i ∈ α.support, a i ^ α i) (p := ∑ i ∈ α.support, α i) (homog_prod ha α α.support) (d := γ) (by` as an intermediate fact. Rewrite using `[hγ]`. Conclude with `fun h' => h h'.symm)`.

Rewrite using `[Finsupp.prod, this, smul_zero]`.
-/
theorem coeff_subst_linear_eq_zero_of_degree {R σ τ : Type} [CommRing R] [Finite σ]
    {a : σ → MvPowerSeries τ R} (ha : ∀ i, (a i).IsHomogeneous 1) {N : ℕ}
    {b : MvPowerSeries σ R} (hb : ∀ α : σ →₀ ℕ, α.degree = N → coeff α b = 0)
    {γ : τ →₀ ℕ} (hγ : γ.degree = N) : coeff γ (subst a b) = 0 := by
  have hs : HasSubst a := hasSubst_of_constantCoeff_zero fun i => by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact IsHomogeneous.coeff_eq_zero (f := a i) (p := 1) (ha i) (by simp)
  rw [coeff_subst hs]
  refine finsum_eq_zero_of_forall_eq_zero fun α => ?_
  by_cases h : α.degree = N
  · rw [hb α h, zero_smul]
  · have := IsHomogeneous.coeff_eq_zero (f := ∏ i ∈ α.support, a i ^ α i)
      (p := ∑ i ∈ α.support, α i) (homog_prod ha α α.support) (d := γ) (by
      rw [hγ]; exact fun h' => h h'.symm)
    rw [Finsupp.prod, this, smul_zero]

/- English proof (translation)
Introduce `R _ d N b hb γ hγ`. Unfold `cob1 inL inR`. Rewrite using `[map_sub, map_sub, coeff_subst_linear_eq_zero_of_degree (a := addLaw R d) (fun i => IsHomogeneous.add (p := 1) (homog_X (Sum.inl i)) (homog_X (Sum.inr i))) hb hγ, coeff_subst_linear_eq_zero_of_degree (fun i => homog_X _) hb hγ, coeff_subst_linear_eq_zero_of_degree (fun i => homog …`. Simplify using the standard rewrite rules.
-/
theorem coeff_cob1_addLaw_eq_zero_of_degree_eq : ∀ (R : Type) [CommRing R] (d N : ℕ)
    (b : MvPowerSeries (Fin d) R), (∀ α : Fin d →₀ ℕ, α.degree = N → coeff α b = 0) →
    ∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → coeff γ (cob1 (addLaw R d) b) = 0 := by
  intro R _ d N b hb γ hγ
  unfold cob1 inL inR
  rw [map_sub, map_sub,
    coeff_subst_linear_eq_zero_of_degree (a := addLaw R d)
      (fun i => IsHomogeneous.add (p := 1) (homog_X (Sum.inl i)) (homog_X (Sum.inr i))) hb hγ,
    coeff_subst_linear_eq_zero_of_degree (fun i => homog_X _) hb hγ,
    coeff_subst_linear_eq_zero_of_degree (fun i => homog_X _) hb hγ]
  simp

end GlobalTheory.Katz
