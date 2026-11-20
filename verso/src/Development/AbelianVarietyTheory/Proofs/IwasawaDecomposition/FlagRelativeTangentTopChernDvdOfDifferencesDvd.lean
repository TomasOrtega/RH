import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordProportionality
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric

namespace GlobalTheory.GoodMetric.DiscrDvd

/- English proof (translation)
Establish `hc : coeff (Finsupp.single a 1) (X a - X b : MvPolynomial σ ℝ) = 1`. Establish `: ¬ (Finsupp.single b 1 = Finsupp.single a 1)` using `fun e => h (Finsupp.single_left_injective one_ne_zero e).symm`. Simplify using `[coeff_X, this]`. Use `irreducible_of_totalDegree_eq_one (le_antisymm ?_ ?_) fun x hx => ?_` and prove the remaining obligations. Conclude with `(totalDegree_sub _ _).trans (by simp)`.

Use `le_totalDegree (p := (X a - X b : MvPolynomial σ ℝ)) (s := Finsupp.single a 1) (by rw [mem_support_iff, hc]; exact one_ne_zero)` as an intermediate fact. Simplify using `using this`. Conclude with `isUnit_of_dvd_one (hc ▸ hx _)`.
-/
theorem irreducible_X_sub_X {σ : Type} {a b : σ} (h : a ≠ b) :
    Irreducible (X a - X b : MvPolynomial σ ℝ) := by
  classical
  have hc : coeff (Finsupp.single a 1) (X a - X b : MvPolynomial σ ℝ) = 1 := by
    have : ¬ (Finsupp.single b 1 = Finsupp.single a 1) := fun e =>
      h (Finsupp.single_left_injective one_ne_zero e).symm
    simp [coeff_X, this]
  refine irreducible_of_totalDegree_eq_one (le_antisymm ?_ ?_) fun x hx => ?_
  · exact (totalDegree_sub _ _).trans (by simp)
  · have := le_totalDegree (p := (X a - X b : MvPolynomial σ ℝ)) (s := Finsupp.single a 1)
      (by rw [mem_support_iff, hc]; exact one_ne_zero)
    simpa using this
  · exact isUnit_of_dvd_one (hc ▸ hx _)

/- English proof (translation)
Use `(irreducible_X_sub_X h).isRelPrime_iff_not_dvd.2 fun hd => ?_` and prove the remaining obligations. Break down `hn with ⟨h1, h2⟩ | ⟨h1, h2⟩` into its components or cases. Use `map_dvd (eval (Pi.single c (1 : ℝ))) hd` as an intermediate fact. Simplify using `[Pi.single_apply, h1.symm, h2.symm, h'.symm] at this`. Use `map_dvd (eval (Pi.single d (1 : ℝ))) hd` as an intermediate fact.

Simplify using `[Pi.single_apply, h1.symm, h2.symm, h'] at this`.
-/
theorem isRelPrime_X_sub_X {σ : Type} {a b c d : σ} (h : a ≠ b) (h' : c ≠ d)
    (hn : (c ≠ a ∧ c ≠ b) ∨ (d ≠ a ∧ d ≠ b)) :
    IsRelPrime (X a - X b : MvPolynomial σ ℝ) (X c - X d) := by
  classical
  refine (irreducible_X_sub_X h).isRelPrime_iff_not_dvd.2 fun hd => ?_
  rcases hn with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have := map_dvd (eval (Pi.single c (1 : ℝ))) hd
    simp [Pi.single_apply, h1.symm, h2.symm, h'.symm] at this
  · have := map_dvd (eval (Pi.single d (1 : ℝ))) hd
    simp [Pi.single_apply, h1.symm, h2.symm, h'] at this

/- English proof (translation)
Establish `ne : ∀ (τ : ι) (i j : Fin (m τ)), i ≠ j → (⟨τ, i⟩ : Root m) ≠ ⟨τ, j⟩` using `fun τ i j h e => h (eq_of_heq (Sigma.mk.inj e).2)`. Unfold `GoodMetric.rootDiscr`. Use `Finset.prod_dvd_of_isRelPrime (fun τ _ τ' _ hτ => ?_) fun τ _ => ?_` and prove the remaining obligations. Use `IsRelPrime.prod_left fun j _ => IsRelPrime.prod_left fun i hi => IsRelPrime.prod_right fun l _ => IsRelPrime.prod_right fun k hk => ?_` and prove the remaining obligations. Use `isRelPrime_X_sub_X (ne _ _ _ (Finset.mem_Iio.1 hi).ne') (ne _ _ _ (Finset.mem_Iio.1 hk).ne') (Or.inl ⟨fun e => hτ (Sigma.mk.inj e).1.symm, fun e => hτ (Sigma.mk.inj e).1.symm⟩)` and prove the remaining obligations.

Use `Finset.prod_dvd_of_isRelPrime (fun j _ l _ hjl => ?_) fun j _ => ?_` and prove the remaining obligations. Use `IsRelPrime.prod_left fun i hi => IsRelPrime.prod_right fun k hk => ?_` and prove the remaining obligations. Establish `hi` using `Finset.mem_Iio.1 hi`. Establish `hk` using `Finset.mem_Iio.1 hk`. Break down `lt_or_gt_of_ne hjl with h | h` into its components or cases.

Conclude with `isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne') (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hi.trans h).ne'⟩)`. Conclude with `(isRelPrime_X_sub_X (ne _ _ _ hk.ne') (ne _ _ _ hi.ne') (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hk.trans h).ne'⟩)).symm`. Use `Finset.prod_dvd_of_isRelPrime (fun i hi k hk hik => ?_) fun i hi => hP τ i j (Finset.mem_Iio.1 hi)` and prove the remaining obligations. Establish `hi` using `Finset.mem_Iio.1 hi`. Establish `hk` using `Finset.mem_Iio.1 hk`.

Conclude with `isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne') (Or.inr ⟨ne _ _ _ hk.ne, ne _ _ _ hik.symm⟩)`.
-/
theorem rootDiscr_dvd (ι : Type) [Fintype ι] (m : ι → ℕ) (P : MvPolynomial (Root m) ℝ)
    (hP : ∀ (τ : ι) (i j : Fin (m τ)), i < j → (X ⟨τ, j⟩ - X ⟨τ, i⟩ : MvPolynomial (Root m) ℝ) ∣ P) :
    GoodMetric.rootDiscr m ∣ P := by
  classical
  have ne : ∀ (τ : ι) (i j : Fin (m τ)), i ≠ j → (⟨τ, i⟩ : Root m) ≠ ⟨τ, j⟩ := fun τ i j h e =>
    h (eq_of_heq (Sigma.mk.inj e).2)
  unfold GoodMetric.rootDiscr
  refine Finset.prod_dvd_of_isRelPrime (fun τ _ τ' _ hτ => ?_) fun τ _ => ?_
  · refine IsRelPrime.prod_left fun j _ => IsRelPrime.prod_left fun i hi =>
      IsRelPrime.prod_right fun l _ => IsRelPrime.prod_right fun k hk => ?_
    refine isRelPrime_X_sub_X (ne _ _ _ (Finset.mem_Iio.1 hi).ne') (ne _ _ _ (Finset.mem_Iio.1 hk).ne')
      (Or.inl ⟨fun e => hτ (Sigma.mk.inj e).1.symm, fun e => hτ (Sigma.mk.inj e).1.symm⟩)
  refine Finset.prod_dvd_of_isRelPrime (fun j _ l _ hjl => ?_) fun j _ => ?_
  · refine IsRelPrime.prod_left fun i hi => IsRelPrime.prod_right fun k hk => ?_
    have hi := Finset.mem_Iio.1 hi
    have hk := Finset.mem_Iio.1 hk
    rcases lt_or_gt_of_ne hjl with h | h
    · exact isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne')
        (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hi.trans h).ne'⟩)
    · exact (isRelPrime_X_sub_X (ne _ _ _ hk.ne') (ne _ _ _ hi.ne')
        (Or.inl ⟨ne _ _ _ h.ne', ne _ _ _ (hk.trans h).ne'⟩)).symm
  refine Finset.prod_dvd_of_isRelPrime (fun i hi k hk hik => ?_) fun i hi => hP τ i j (Finset.mem_Iio.1 hi)
  have hi := Finset.mem_Iio.1 hi
  have hk := Finset.mem_Iio.1 hk
  exact isRelPrime_X_sub_X (ne _ _ _ hi.ne') (ne _ _ _ hk.ne')
    (Or.inr ⟨ne _ _ _ hk.ne, ne _ _ _ hik.symm⟩)

end GlobalTheory.GoodMetric.DiscrDvd
