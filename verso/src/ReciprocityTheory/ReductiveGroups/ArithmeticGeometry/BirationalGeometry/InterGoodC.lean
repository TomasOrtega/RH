import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodB

namespace ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial

/- English proof (translation)
Establish `hdom` using `isDomain_qQuot P hP hH`. Take `⟨s, g, hinj, hint⟩` from `exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ qIdeal P)`. Establish `hns : n ≤ s` using `by set S := Algebra.adjoin ℚ (Set.range (g ∘ X))`. Establish `hmem : ∀ y, g y ∈ S`. Introduce `y`.

Use `show g y ∈ Algebra.adjoin ℚ (Set.range (g ∘ X))`. Rewrite using `[Algebra.adjoin_range_eq_range_aeval]`. Use `⟨y, ?_⟩` and prove the remaining obligations. Use `show aeval (g ∘ X) y = g y`. Rewrite using `[← MvPolynomial.aeval_unique g]`.

Set `g' : MvPolynomial (Fin s) ℚ →+* S` to `g.toRingHom.codRestrict S.toSubsemiring hmem`. Establish `hg' : (algebraMap S (MvPolynomial σ ℚ ⧸ qIdeal P)).comp g' = g.toRingHom`. Apply the tactic sequence `ext y <;> rfl`. Establish `halg : Algebra.IsAlgebraic S (MvPolynomial σ ℚ ⧸ qIdeal P)`. Use `⟨fun b => ?_⟩` and prove the remaining obligations.

Take `⟨p, hpm, hp⟩` from `hint b`. Use `IsIntegral.isAlgebraic ⟨p.map g', hpm.map g', ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.eval₂_map, hg']`. Conclude with `hp`. Establish `h1` using `hx.cardinalMk_le_trdeg`.

Establish `h2` using `Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ (Set.range (g ∘ X))`. Establish `h3` using `Cardinal.mk_range_le (f := g ∘ X)`. Use `h1.trans (h2.trans h3)` as an intermediate fact. Simplify using `using this`. Establish `hdim : (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℚ ⧸ qIdeal P)`.

Use `le_ringKrullDim_of_isIntegral g.toRingHom hint hinj s ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]`. Simplify using the standard rewrite rules. Use `letI := (ratHom P).toAlgebra`. Use `haveI := ratHom_isLocalization P`.

Use `succ_le_ringKrullDim_of_isLocalization (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ)) ?_ n (le_trans (by exact_mod_cast hns) hdim)` and prove the remaining obligations. Introduce `p hp hdis`. Use `exists_gt_of_comap_int_eq_bot (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective p hp ?_` and prove the remaining obligations. Use extensionality with `m`. Simplify using `only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, Submodule.mem_bot]`.

Prove the components needed by the constructor for the conclusion. Introduce `hm`. Assume the negation of the conclusion as `hm0`. Use `Set.disjoint_left.mp hdis ⟨m, mem_nonZeroDivisors_of_ne_zero hm0, rfl⟩ ?_` and prove the remaining obligations. Simplify `hm` using `[eq_intCast]`.

Introduce and unpack `rfl`. Simplify using the standard rewrite rules.
-/
theorem succ_le_ringKrullDim_of_algebraicIndependent {σ : Type} [Finite σ]
    (P : Ideal (MvPolynomial σ ℤ)) (hP : P.IsPrime)
    (hH : P.comap (C : ℤ →+* MvPolynomial σ ℤ) = ⊥) {n : ℕ}
    (x : Fin n → MvPolynomial σ ℚ ⧸ qIdeal P) (hx : AlgebraicIndependent ℚ x) :
    ((n + 1 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℤ ⧸ P) := by
  have hdom := isDomain_qQuot P hP hH
  obtain ⟨s, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg ℚ (MvPolynomial σ ℚ ⧸ qIdeal P)
  have hns : n ≤ s := by
    set S := Algebra.adjoin ℚ (Set.range (g ∘ X))
    have hmem : ∀ y, g y ∈ S := by
      intro y
      show g y ∈ Algebra.adjoin ℚ (Set.range (g ∘ X))
      rw [Algebra.adjoin_range_eq_range_aeval]
      refine ⟨y, ?_⟩
      show aeval (g ∘ X) y = g y
      rw [← MvPolynomial.aeval_unique g]
    let g' : MvPolynomial (Fin s) ℚ →+* S := g.toRingHom.codRestrict S.toSubsemiring hmem
    have hg' : (algebraMap S (MvPolynomial σ ℚ ⧸ qIdeal P)).comp g' = g.toRingHom := by
      ext y <;> rfl
    have halg : Algebra.IsAlgebraic S (MvPolynomial σ ℚ ⧸ qIdeal P) := by
      refine ⟨fun b => ?_⟩
      obtain ⟨p, hpm, hp⟩ := hint b
      refine IsIntegral.isAlgebraic ⟨p.map g', hpm.map g', ?_⟩
      rw [Polynomial.eval₂_map, hg']
      exact hp
    have h1 := hx.cardinalMk_le_trdeg
    have h2 := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ (Set.range (g ∘ X))
    have h3 := Cardinal.mk_range_le (f := g ∘ X)
    have := h1.trans (h2.trans h3)
    simpa using this
  have hdim : (s : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial σ ℚ ⧸ qIdeal P) := by
    refine le_ringKrullDim_of_isIntegral g.toRingHom hint hinj s ?_
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  letI := (ratHom P).toAlgebra
  haveI := ratHom_isLocalization P
  refine succ_le_ringKrullDim_of_isLocalization
    (Algebra.algebraMapSubmonoid (MvPolynomial σ ℤ ⧸ P) (nonZeroDivisors ℤ)) ?_ n
    (le_trans (by exact_mod_cast hns) hdim)
  intro p hp hdis
  refine exists_gt_of_comap_int_eq_bot (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective p hp ?_
  ext m
  simp only [Ideal.mem_comap, RingHom.coe_comp, Function.comp_apply, Submodule.mem_bot]
  constructor
  · intro hm
    by_contra hm0
    refine Set.disjoint_left.mp hdis ⟨m, mem_nonZeroDivisors_of_ne_zero hm0, rfl⟩ ?_
    simpa [eq_intCast] using hm
  · rintro rfl
    simp

end ReciprocityTheory.ChartRestriction.G.Geo
