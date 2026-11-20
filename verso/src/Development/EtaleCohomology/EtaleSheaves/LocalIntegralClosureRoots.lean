import Development.EtaleCohomology.EtaleSheaves.IntegralNormalization.NormAICOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry LateralTheory.E.t_E2Cut Polynomial

namespace LateralTheory.E.LocalIntegralClosureRoots

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hn hp x hx`. Establish `h1` using `Polynomial.eq_one_of_monic_natDegree_zero hp hn`.

Substitute `h1` using the available equality. Simplify using `at hx`. Consider the case `succ n ih`. Introduce `p hn hp x hx`. Take `⟨a, ha⟩` from `h p hp (by omega)`.

Establish `hdvd : (X - C a) * (p /ₘ (X - C a)) = p` using `mul_divByMonic_eq_iff_isRoot.mpr ha`. Establish `hq : (p /ₘ (X - C a)).Monic` using `(monic_X_sub_C a).of_mul_monic_left (by rw [hdvd]; exact hp)`. Establish `hqd : (p /ₘ (X - C a)).natDegree = n`. Rewrite using `[natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers.

Rewrite `hx` using `[← hdvd, map_mul]`. Break down `mul_eq_zero.mp hx with h1 | h1` into its components or cases. Use `⟨a, ?_⟩` and prove the remaining obligations. Simplify using `only [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1`. Conclude with `h1.symm`.

Conclude with `ih _ hqd hq x h1`.
-/
theorem root_mem (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] (h : GlobalTheory.EtC.AIC A) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → ∀ x : K, aeval x p = 0 →
      ∃ a : A, algebraMap A K a = x := by
  intro n
  induction n with
  | zero =>
    intro p hn hp x hx
    have h1 := Polynomial.eq_one_of_monic_natDegree_zero hp hn
    subst h1
    simp at hx
  | succ n ih =>
    intro p hn hp x hx
    obtain ⟨a, ha⟩ := h p hp (by omega)
    have hdvd : (X - C a) * (p /ₘ (X - C a)) = p := mul_divByMonic_eq_iff_isRoot.mpr ha
    have hq : (p /ₘ (X - C a)).Monic := (monic_X_sub_C a).of_mul_monic_left (by rw [hdvd]; exact hp)
    have hqd : (p /ₘ (X - C a)).natDegree = n := by
      rw [natDegree_divByMonic _ (monic_X_sub_C a), natDegree_X_sub_C]; omega
    rw [← hdvd, map_mul] at hx
    rcases mul_eq_zero.mp hx with h1 | h1
    · refine ⟨a, ?_⟩
      simp only [map_sub, aeval_X, aeval_C, sub_eq_zero] at h1
      exact h1.symm
    · exact ih _ hqd hq x h1

/- English proof (translation)
Rewrite using `[isIntegrallyClosed_iff (FractionRing A)]`. Introduce `x ⟨p, hp, hx⟩`. Conclude with `root_mem A (FractionRing A) h _ p rfl hp x (by rw [aeval_def]; exact hx)`.
-/
theorem isIntegrallyClosed_of_aic (A : Type) [CommRing A] [IsDomain A] (h : GlobalTheory.EtC.AIC A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro x ⟨p, hp, hx⟩
  exact root_mem A (FractionRing A) h _ p rfl hp x (by rw [aeval_def]; exact hx)

/- English proof (translation)
Introduce `X _ hcov`. Use `⟨inferInstance, fun V hV hVne => ?_⟩` and prove the remaining obligations. Establish `: Nonempty V` using `hVne.to_subtype`. Establish `hst : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)`. Introduce `x`.

Take `⟨U, hxU, hU, hA⟩` from `hcov x`. Establish `: Nonempty U` using `⟨⟨x, hxU⟩⟩`. Use `isIntegrallyClosed_of_aic _ hA` as an intermediate fact. Set `` to `TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)`. Use `hU.isLocalization_stalk ⟨x, hxU⟩` as an intermediate fact.

Conclude with `isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)`. Establish `hR : IsIntegrallyClosed Γ(X, V)`. Apply `IsIntegrallyClosed.of_localization_maximal` to reduce the goal to its premises. Introduce `P _ hP`. Set `y : PrimeSpectrum Γ(X, V)` to `⟨P, hP.isPrime⟩`.

Establish `hy : hV.fromSpec y ∈ V` using `by show hV.fromSpec y ∈ (V : Set X)`. Rewrite using `[← hV.range_fromSpec]`. Conclude with `⟨y, rfl⟩`. Set `` to `TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hV.fromSpec y, hy⟩ : V)`. Establish `: IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) P` using `hV.isLocalization_stalk' y hy`.

Use `hst (hV.fromSpec y)` as an intermediate fact. Conclude with `IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv P.primeCompl (X.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime P)).toRingEquiv`. Establish `hK : IsAlgClosed X.functionField`. Take `⟨x⟩` from `‹Nonempty V›`. Take `⟨U, hxU, hU, hA⟩` from `hcov x.1`.

Establish `: Nonempty U` using `⟨⟨x.1, hxU⟩⟩`. Use `functionField_isFractionRing_of_isAffineOpen X U hU` as an intermediate fact. Conclude with `NormPf.FFPf.algClosed_of_aic _ _ hA`. Use `functionField_isFractionRing_of_isAffineOpen X V hV` as an intermediate fact. Introduce `p hp hd`.

Take `⟨z, hz⟩` from `IsAlgClosed.exists_root (p.map (algebraMap Γ(X, V) X.functionField)) (by`. Rewrite using `[degree_map_eq_of_injective (IsFractionRing.injective Γ(X, V) X.functionField), degree_eq_natDegree hp.ne_zero]`. Conclude with `hd.ne')` after adjusting the coercions. Establish `hint : IsIntegral Γ(X, V) z` using `⟨p, hp, by rwa [IsRoot, Polynomial.eval_map] at hz⟩`. Take `⟨a, ha⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`.

Use `⟨a, IsFractionRing.injective Γ(X, V) X.functionField ?_⟩` and prove the remaining obligations. Establish `hz' : eval z (p.map (algebraMap Γ(X, V) X.functionField)) = 0` using `hz`. Rewrite using `[map_zero, ← hz', Polynomial.eval_map, ← ha, eval₂_at_apply]`.
-/
theorem LocAIC_of : NormPf.AICPf.LocAIC := by
  intro X _ hcov
  refine ⟨inferInstance, fun V hV hVne => ?_⟩
  have : Nonempty V := hVne.to_subtype
  have hst : ∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x) := by
    intro x
    obtain ⟨U, hxU, hU, hA⟩ := hcov x
    have : Nonempty U := ⟨⟨x, hxU⟩⟩
    have := isIntegrallyClosed_of_aic _ hA
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U)
    have := hU.isLocalization_stalk ⟨x, hxU⟩
    exact isIntegrallyClosed_of_isLocalization (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  have hR : IsIntegrallyClosed Γ(X, V) := by
    apply IsIntegrallyClosed.of_localization_maximal
    intro P _ hP
    let y : PrimeSpectrum Γ(X, V) := ⟨P, hP.isPrime⟩
    have hy : hV.fromSpec y ∈ V := by
      show hV.fromSpec y ∈ (V : Set X)
      rw [← hV.range_fromSpec]; exact ⟨y, rfl⟩
    let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨hV.fromSpec y, hy⟩ : V)
    have : IsLocalization.AtPrime (X.presheaf.stalk (hV.fromSpec y)) P := hV.isLocalization_stalk' y hy
    have := hst (hV.fromSpec y)
    exact IsIntegrallyClosed.of_equiv (IsLocalization.algEquiv P.primeCompl
      (X.presheaf.stalk (hV.fromSpec y)) (Localization.AtPrime P)).toRingEquiv
  have hK : IsAlgClosed X.functionField := by
    obtain ⟨x⟩ := ‹Nonempty V›
    obtain ⟨U, hxU, hU, hA⟩ := hcov x.1
    have : Nonempty U := ⟨⟨x.1, hxU⟩⟩
    have := functionField_isFractionRing_of_isAffineOpen X U hU
    exact NormPf.FFPf.algClosed_of_aic _ _ hA
  have := functionField_isFractionRing_of_isAffineOpen X V hV
  intro p hp hd
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (p.map (algebraMap Γ(X, V) X.functionField))
    (by
      rw [degree_map_eq_of_injective (IsFractionRing.injective Γ(X, V) X.functionField),
        degree_eq_natDegree hp.ne_zero]
      exact_mod_cast hd.ne')
  have hint : IsIntegral Γ(X, V) z := ⟨p, hp, by rwa [IsRoot, Polynomial.eval_map] at hz⟩
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨a, IsFractionRing.injective Γ(X, V) X.functionField ?_⟩
  have hz' : eval z (p.map (algebraMap Γ(X, V) X.functionField)) = 0 := hz
  rw [map_zero, ← hz', Polynomial.eval_map, ← ha, eval₂_at_apply]

end LateralTheory.E.LocalIntegralClosureRoots

end
