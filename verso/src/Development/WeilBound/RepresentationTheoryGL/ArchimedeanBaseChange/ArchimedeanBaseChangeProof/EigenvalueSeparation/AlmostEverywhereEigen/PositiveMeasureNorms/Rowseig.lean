import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open MeasureTheory
open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

/- English proof (translation)
Introduce `hAe hUn X ι _ Φ T T₁ k u u' hΦ hT hk heq x i`. Establish `wc : ∀ j, Continuous fun y => inner ℂ (k j y) u` using `fun j => (hk.cont j).inner continuous_const`. Establish `winv : ∀ j, ∀ γ ∈ X.Γ, ∀ y, (fun y => inner ℂ (k j y) u) (γ * y) = (fun y => inner ℂ (k j y) u) y` using `fun j γ hγ y => by simp only [hk.inv j γ hγ y]`. Establish `hLc : Continuous fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ` using `continuous_finsetSum _ fun j _ => (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).2`. Establish `hRc : Continuous fun x => inner ℂ (k i x) u'` using `(hk.cont i).inner continuous_const`.

Establish `hLinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) (γ * x) = (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) x`. Introduce `γ hγ x`. Use `Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only [mul_assoc, hk.inv j γ hγ]`. Establish `hRinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => inner ℂ (k i x) u') (γ * x) = (fun x => inner ℂ (k i x) u') x` using `fun γ hγ x => by simp only [hk.inv i γ hγ x]`.

Establish `h3 : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) = fun x => ∑ j, ∫ y, ker X.Γ (Φ i j) x y * (T₁ u j : X.G → ℂ) y ∂X.ν`. Use function extensionality and compare the values at `x`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e1` using `(hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).1 x`. Use `e1.symm.trans (integral_congr_ae ((hk.rep u j).mono fun y hy => ?_))` and prove the remaining obligations.

Simplify using `only [hy]`. Establish `hae : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) =ᵐ[X.ν] fun x => inner ℂ (k i x) u'`. Rewrite using `[h3]`. Establish `h1` using `hT (T₁ u) i`. Rewrite `h1` using `[heq]`.

Conclude with `h1.symm.trans (hk.rep u' i)`. Conclude with `congrFun (hAe X _ _ hLc hRc hLinv hRinv hae) x`.
-/
theorem rowseig : AeEq → Unfold → RowsEig := by
  intro hAe hUn X ι _ Φ T T₁ k u u' hΦ hT hk heq x i
  have wc : ∀ j, Continuous fun y => inner ℂ (k j y) u := fun j => (hk.cont j).inner continuous_const
  have winv : ∀ j, ∀ γ ∈ X.Γ, ∀ y, (fun y => inner ℂ (k j y) u) (γ * y) = (fun y => inner ℂ (k j y) u) y :=
    fun j γ hγ y => by simp only [hk.inv j γ hγ y]
  have hLc : Continuous fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ :=
    continuous_finsetSum _ fun j _ => (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).2
  have hRc : Continuous fun x => inner ℂ (k i x) u' := (hk.cont i).inner continuous_const
  have hLinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) (γ * x)
      = (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) x := by
    intro γ hγ x
    refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [mul_assoc, hk.inv j γ hγ]
  have hRinv : ∀ γ ∈ X.Γ, ∀ x, (fun x => inner ℂ (k i x) u') (γ * x) = (fun x => inner ℂ (k i x) u') x :=
    fun γ hγ x => by simp only [hk.inv i γ hγ x]
  have h3 : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ)
      = fun x => ∑ j, ∫ y, ker X.Γ (Φ i j) x y * (T₁ u j : X.G → ℂ) y ∂X.ν := by
    funext x
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 := (hUn X (Φ i j) _ (hΦ i j) (wc j) (winv j)).1 x
    refine e1.symm.trans (integral_congr_ae ((hk.rep u j).mono fun y hy => ?_))
    simp only [hy]
  have hae : (fun x => ∑ j, ∫ y, Φ i j y * inner ℂ (k j (x * y)) u ∂X.μ) =ᵐ[X.ν]
      fun x => inner ℂ (k i x) u' := by
    rw [h3]
    have h1 := hT (T₁ u) i
    rw [heq] at h1
    exact h1.symm.trans (hk.rep u' i)
  exact congrFun (hAe X _ _ hLc hRc hLinv hRinv hae) x

end PositivityTheory.Rg.BcB.E2.P
