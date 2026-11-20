import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use `set bad : J → Finset (ι → Fin (n + 1)) := fun j => Finset.univ.filter fun c => ‖∑ a, ((c a : ℕ) : ℂ) * v j a‖ < ε / 2 with hbad`. Use `set N := Fintype.card (ι → Fin (n + 1)) with hN`. Establish `hNpos : 0 < N` using `Fintype.card_pos`.

Establish `h1 : ∀ j ∈ T, (bad j).card * (n + 1) ≤ N`. Introduce `j hj`. Take `⟨a, ha⟩` from `hv j hj`. Establish `hinj : Set.InjOn (fun p : (ι → Fin (n + 1)) × Fin (n + 1) => Function.update p.1 a p.2) ((bad j ×ˢ (Finset.univ : Finset (Fin (n + 1))) : Finset _) : Set _)`. Introduce and unpack `⟨c, k⟩ hc ⟨c', k'⟩ hc' h`.

Simplify using `only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hbad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_univ, Set.mem_univ, and_true] at hc hc'`. Establish `hk : k = k'` using `by simpa using congrFun h a`. Establish `hoff : ∀ b, b ≠ a → c b = c' b` using `fun b hb => by`. Simplify `congrFun h b` using `[Function.update_of_ne hb]`. Establish `hsum : (∑ b, ((c b : ℕ) : ℂ) * v j b) - ∑ b, ((c' b : ℕ) : ℂ) * v j b = ((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a`.

Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_eq_single a]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `b _ hb`. Rewrite using `[hoff b hb]`.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Establish `hlt : ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a‖ < ε`. Rewrite using `[← hsum]`. Use `norm_sub_le (∑ b, ((c b : ℕ) : ℂ) * v j b) (∑ b, ((c' b : ℕ) : ℂ) * v j b)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hca : c a = c' a`. Assume the negation of the conclusion as `hne`. Establish `hz : (((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) ≠ 0`. Introduce `h0`.

Apply `hne` to reduce the goal to its premises. Apply `Fin.ext` to reduce the goal to its premises. Use linear arithmetic over natural numbers and integers. Establish `h1 : (1 : ℝ) ≤ ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ)‖`. Rewrite using `[Complex.norm_intCast]`.

Conclude with `Int.one_le_abs hz` after adjusting the coercions. Rewrite `hlt` using `[norm_mul]`. Use polynomial arithmetic with `[norm_nonneg (v j a)]`. Use `Prod.ext ?_ hk` and prove the remaining obligations. Use function extensionality and compare the values at `b`.

Distinguish the cases in `hb : b = a`. Substitute `hb` using the available equality. Conclude with `hca`. Conclude with `hoff b hb`. Use `Finset.card_le_card_of_injOn _ (t := Finset.univ) (fun _ _ => by simp) hinj` as an intermediate fact.

Simplify `this` using `[hN]`. Establish `h2 : (Finset.univ : Finset (ι → Fin (n + 1))) ⊆ T.biUnion bad`. Introduce `c _`. Take `⟨j, hj, h⟩` from `hcon c`. Conclude with `Finset.mem_biUnion.2 ⟨j, hj, by simpa [hbad] using h⟩`.

Establish `h3 : N ≤ ∑ j ∈ T, (bad j).card` using `(Finset.card_le_card h2).trans Finset.card_biUnion_le`. Establish `h4 : N * (n + 1) ≤ T.card * N`. Combine the equalities or inequalities in the displayed calculation. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exists_natForm_norm_ge {ι J : Type*} [Fintype ι] [DecidableEq ι] (T : Finset J) (n : ℕ)
    (hn : T.card ≤ n) (v : J → ι → ℂ) (ε : ℝ) (hv : ∀ j ∈ T, ∃ a, ε ≤ ‖v j a‖) :
    ∃ c : ι → Fin (n + 1), ∀ j ∈ T, ε / 2 ≤ ‖∑ a, ((c a : ℕ) : ℂ) * v j a‖ := by
  classical
  by_contra hcon
  push Not at hcon
  set bad : J → Finset (ι → Fin (n + 1)) := fun j =>
    Finset.univ.filter fun c => ‖∑ a, ((c a : ℕ) : ℂ) * v j a‖ < ε / 2 with hbad
  set N := Fintype.card (ι → Fin (n + 1)) with hN
  have hNpos : 0 < N := Fintype.card_pos
  have h1 : ∀ j ∈ T, (bad j).card * (n + 1) ≤ N := by
    intro j hj
    obtain ⟨a, ha⟩ := hv j hj
    have hinj : Set.InjOn (fun p : (ι → Fin (n + 1)) × Fin (n + 1) => Function.update p.1 a p.2)
        ((bad j ×ˢ (Finset.univ : Finset (Fin (n + 1))) : Finset _) : Set _) := by
      rintro ⟨c, k⟩ hc ⟨c', k'⟩ hc' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, hbad, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.coe_univ, Set.mem_univ, and_true] at hc hc'
      have hk : k = k' := by simpa using congrFun h a
      have hoff : ∀ b, b ≠ a → c b = c' b := fun b hb => by
        simpa [Function.update_of_ne hb] using congrFun h b
      have hsum : (∑ b, ((c b : ℕ) : ℂ) * v j b) - ∑ b, ((c' b : ℕ) : ℂ) * v j b
          = ((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
        · push_cast; ring
        · intro b _ hb; rw [hoff b hb]; ring
        · simp
      have hlt : ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ) * v j a‖ < ε := by
        rw [← hsum]
        have := norm_sub_le (∑ b, ((c b : ℕ) : ℂ) * v j b) (∑ b, ((c' b : ℕ) : ℂ) * v j b)
        linarith
      have hca : c a = c' a := by
        by_contra hne
        have hz : (((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) ≠ 0 := by
          intro h0
          apply hne
          apply Fin.ext
          omega
        have h1 : (1 : ℝ) ≤ ‖((((c a : ℕ) : ℤ) - ((c' a : ℕ) : ℤ) : ℤ) : ℂ)‖ := by
          rw [Complex.norm_intCast]
          exact_mod_cast Int.one_le_abs hz
        rw [norm_mul] at hlt
        nlinarith [norm_nonneg (v j a)]
      refine Prod.ext ?_ hk
      funext b
      by_cases hb : b = a
      · subst hb; exact hca
      · exact hoff b hb
    have := Finset.card_le_card_of_injOn _ (t := Finset.univ) (fun _ _ => by simp) hinj
    simpa [hN] using this
  have h2 : (Finset.univ : Finset (ι → Fin (n + 1))) ⊆ T.biUnion bad := by
    intro c _
    obtain ⟨j, hj, h⟩ := hcon c
    exact Finset.mem_biUnion.2 ⟨j, hj, by simpa [hbad] using h⟩
  have h3 : N ≤ ∑ j ∈ T, (bad j).card := (Finset.card_le_card h2).trans Finset.card_biUnion_le
  have h4 : N * (n + 1) ≤ T.card * N := by
    calc N * (n + 1) ≤ (∑ j ∈ T, (bad j).card) * (n + 1) := Nat.mul_le_mul_right _ h3
      _ = ∑ j ∈ T, (bad j).card * (n + 1) := Finset.sum_mul ..
      _ ≤ ∑ j ∈ T, N := Finset.sum_le_sum h1
      _ = T.card * N := by simp
  nlinarith

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `hs` using `IsAlgClosed.splits p`. Rewrite `h` using `[hs.eval_eq_prod_roots_of_monic hp, hs.natDegree_eq_card_roots]`. Establish `key : ∀ s : Multiset ℂ, (∀ r ∈ s, δ ≤ ‖r - x‖) → δ ^ s.card ≤ ‖(s.map fun r => x - r).prod‖`.

Introduce `s`. Proceed by induction on `s using Multiset.induction_on with`. Consider the case `empty => simp`. Consider the case `cons a s ih`. Introduce `hs`.

Simplify using `only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, pow_succ']`. Use `mul_le_mul ?_ (ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)) (by positivity) (norm_nonneg _)` and prove the remaining obligations. Rewrite using `[norm_sub_rev]`. Conclude with `hs a (Multiset.mem_cons_self _ _)`. Conclude with `absurd h (not_lt.2 (key _ fun r hr => hcon r (Polynomial.isRoot_of_mem_roots hr)))`.
-/
theorem exists_root_near_of_norm_eval_lt (p : Polynomial ℂ) (hp : p.Monic) (x : ℂ) (δ : ℝ)
    (hδ : 0 < δ) (h : ‖p.eval x‖ < δ ^ p.natDegree) : ∃ r, p.IsRoot r ∧ ‖r - x‖ < δ := by
  by_contra hcon
  push Not at hcon
  have hs := IsAlgClosed.splits p
  rw [hs.eval_eq_prod_roots_of_monic hp, hs.natDegree_eq_card_roots] at h
  have key : ∀ s : Multiset ℂ, (∀ r ∈ s, δ ≤ ‖r - x‖) →
      δ ^ s.card ≤ ‖(s.map fun r => x - r).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | cons a s ih =>
      intro hs
      simp only [Multiset.card_cons, Multiset.map_cons, Multiset.prod_cons, norm_mul, pow_succ']
      refine mul_le_mul ?_ (ih fun r hr => hs r (Multiset.mem_cons_of_mem hr)) (by positivity)
        (norm_nonneg _)
      rw [norm_sub_rev]
      exact hs a (Multiset.mem_cons_self _ _)
  exact absurd h (not_lt.2 (key _ fun r hr => hcon r (Polynomial.isRoot_of_mem_roots hr)))

/- English proof (translation)
Set `_ : Algebra R Ω` to `((algebraMap A Ω).comp (algebraMap R A)).toAlgebra`. Establish `: IsScalarTower R A Ω` using `IsScalarTower.of_algebraMap_eq fun _ => rfl`. Establish `: FaithfulSMul R Ω` using `(faithfulSMul_iff_algebraMap_injective R Ω).2 ((IsFractionRing.injective A Ω).comp (FaithfulSMul.algebraMap_injective R A))`. Set `F` to `FractionRing R`. Set `_ : Algebra F Ω` to `FractionRing.liftAlgebra R Ω`.

Establish `: IsScalarTower R F Ω` using `FractionRing.isScalarTower_liftAlgebra R Ω`. Establish `: IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) Ω` using `inferInstance`. Establish `: FiniteDimensional F Ω` using `Module.Finite.of_isLocalization R A (nonZeroDivisors R)`. Use `⟨Module.finrank F Ω, fun τ hτ => ?_⟩` and prove the remaining obligations. Set `_ : Algebra F ℂ` to `(IsFractionRing.lift hτ : F →+* ℂ).toAlgebra`.

Establish `hF : ∀ x : R, algebraMap F ℂ (algebraMap R F x) = τ x` using `fun x => IsFractionRing.lift_algebraMap hτ x`. Set `_ : Fintype (Ω →ₐ[F] ℂ)` to `Fintype.ofFinite _`. Use `⟨Finset.univ.image fun ψ : Ω →ₐ[F] ℂ => (ψ : Ω →+* ℂ), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `Finset.card_image_le.trans ?_` and prove the remaining obligations. Rewrite using `[Finset.card_univ, ← Nat.card_eq_fintype_card]`.

Conclude with `card_algHom_le_finrank F Ω ℂ`. Introduce `σ hσ`. Take `⟨ψ, -, rfl⟩` from `Finset.mem_image.1 hσ`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `ψ (algebraMap R Ω x) = τ x`.

Rewrite using `[IsScalarTower.algebraMap_apply R F Ω, AlgHom.commutes, hF]`. Introduce `b r hr`. Establish `hb : IsIntegral R b` using `Algebra.IsIntegral.isIntegral b`. Establish `h1 : r ∈ (minpoly F (algebraMap A Ω b)).rootSet ℂ`. Rewrite using `[Polynomial.mem_rootSet]`.

Use `⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩` and prove the remaining obligations. Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions F Ω hb, Polynomial.aeval_def, Polynomial.eval₂_map, show (algebraMap F ℂ).comp (algebraMap R F) = τ from RingHom.ext hF, Polynomial.eval₂_eq_eval_map]`. Conclude with `hr`. Rewrite `h1` using `[← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ]`. Take `⟨ψ, hψ⟩` from `h1`.

Conclude with `⟨ψ, Finset.mem_image.2 ⟨ψ, Finset.mem_univ _, rfl⟩, hψ⟩`.
-/
theorem exists_embeddings_over_injective (R A Ω : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CommRing A] [IsDomain A] [Algebra R A] [Module.Finite R A]
    [FaithfulSMul R A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] :
    ∃ n : ℕ, ∀ τ : R →+* ℂ, Function.Injective τ → ∃ T : Finset (Ω →+* ℂ), T.card ≤ n ∧
      (∀ σ ∈ T, σ.comp ((algebraMap A Ω).comp (algebraMap R A)) = τ) ∧
      ∀ (b : A) (r : ℂ), ((minpoly R b).map τ).IsRoot r → ∃ σ ∈ T, σ (algebraMap A Ω b) = r := by
  classical
  let _ : Algebra R Ω := ((algebraMap A Ω).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FaithfulSMul R Ω := (faithfulSMul_iff_algebraMap_injective R Ω).2
    ((IsFractionRing.injective A Ω).comp (FaithfulSMul.algebraMap_injective R A))
  let F := FractionRing R
  let _ : Algebra F Ω := FractionRing.liftAlgebra R Ω
  have : IsScalarTower R F Ω := FractionRing.isScalarTower_liftAlgebra R Ω
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors R)) Ω :=
    inferInstance
  have : FiniteDimensional F Ω := Module.Finite.of_isLocalization R A (nonZeroDivisors R)
  refine ⟨Module.finrank F Ω, fun τ hτ => ?_⟩
  let _ : Algebra F ℂ := (IsFractionRing.lift hτ : F →+* ℂ).toAlgebra
  have hF : ∀ x : R, algebraMap F ℂ (algebraMap R F x) = τ x := fun x =>
    IsFractionRing.lift_algebraMap hτ x
  let _ : Fintype (Ω →ₐ[F] ℂ) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun ψ : Ω →ₐ[F] ℂ => (ψ : Ω →+* ℂ), ?_, ?_, ?_⟩
  · refine Finset.card_image_le.trans ?_
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact card_algHom_le_finrank F Ω ℂ
  · intro σ hσ
    obtain ⟨ψ, -, rfl⟩ := Finset.mem_image.1 hσ
    ext x
    change ψ (algebraMap R Ω x) = τ x
    rw [IsScalarTower.algebraMap_apply R F Ω, AlgHom.commutes, hF]
  · intro b r hr
    have hb : IsIntegral R b := Algebra.IsIntegral.isIntegral b
    have h1 : r ∈ (minpoly F (algebraMap A Ω b)).rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero (Algebra.IsIntegral.isIntegral _), ?_⟩
      rw [minpoly.isIntegrallyClosed_eq_field_fractions F Ω hb, Polynomial.aeval_def,
        Polynomial.eval₂_map, show (algebraMap F ℂ).comp (algebraMap R F) = τ from RingHom.ext hF,
        Polynomial.eval₂_eq_eval_map]
      exact hr
    rw [← Algebra.IsAlgebraic.range_eval_eq_rootSet_minpoly ℂ] at h1
    obtain ⟨ψ, hψ⟩ := h1
    exact ⟨ψ, Finset.mem_image.2 ⟨ψ, Finset.mem_univ _, rfl⟩, hψ⟩

/- English proof (translation)
Simplify using `only [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]`. Use `continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const` and prove the remaining obligations. Simplify using `only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]`. Conclude with `MvPolynomial.continuous_eval _`.
-/
theorem continuous_eval_map_eval₂Hom {K : Type*} [CommRing K] (sg : K →+* ℂ) {D : ℕ}
    (μ : Polynomial (MvPolynomial (Fin D) K)) (x : ℂ) :
    Continuous fun z : Fin D → ℂ => (μ.map (MvPolynomial.eval₂Hom sg z)).eval x := by
  simp only [Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  refine continuous_finsetSum _ fun i _ => Continuous.mul ?_ continuous_const
  simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map]
  exact MvPolynomial.continuous_eval _

/- English proof (translation)
Introduce `hgen K A Ω _ _ _ _ _ _ _ _ _ _ _ sg φ hφ S ε hε`. Take `⟨D, g, hinj, hfin⟩` from `exists_finite_inj_algHom_of_fg K A`. Set `R` to `MvPolynomial (Fin D) K`. Set `_ : Algebra R A` to `g.toRingHom.toAlgebra`. Establish `: Module.Finite R A` using `hfin`.

Establish `: FaithfulSMul R A` using `(faithfulSMul_iff_algebraMap_injective R A).2 hinj`. Establish `: Countable K` using `Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.toEquiv.symm`. Take `⟨n, hn⟩` from `exists_embeddings_over_injective R A Ω`. Set `z₀ : Fin D → ℂ` to `fun i => φ (g (MvPolynomial.X i))`. Establish `hz₀ : MvPolynomial.eval₂Hom sg z₀ = φ.comp (algebraMap R A)`.

Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `k`. Express the relevant statement in the definitionally equal form `_ = φ (g (algebraMap K _ k))`. Rewrite using `[AlgHom.commutes, ← hφ]`. Simplify using the standard rewrite rules.

Introduce `i`. Simplify using `only [MvPolynomial.eval₂Hom_X']`. Both sides reduce to the same expression. Set `b : (S → Fin (n + 1)) → A` to `fun c => ∑ a : S, ((c a : ℕ) : A) * (a : A)`. Establish `hev : ∀ᶠ z in nhds z₀, ∀ c, ‖((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z)).eval (φ (b c))‖ < (ε / 2) ^ (minpoly R (b c)).natDegree`.

Rewrite using `[Filter.eventually_all]`. Introduce `c`. Use `((continuous_eval_map_eval₂Hom sg (minpoly R (b c)) (φ (b c))).norm.tendsto z₀).eventually_lt_const ?_` and prove the remaining obligations. Establish `h0 : ((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z₀)).eval (φ (b c)) = 0`. Rewrite using `[hz₀, Polynomial.eval_map, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, minpoly.aeval, map_zero]`.

Simplify using `only [h0, norm_zero]`. Check the signs of the components of the expression. Take `⟨η, hη, hball⟩` from `Metric.eventually_nhds_iff.1 hev`. Take `⟨z, hz, hzg⟩` from `hgen K sg D z₀ η hη`. Establish `hτ : Function.Injective (MvPolynomial.eval₂Hom sg z)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `p hp`. Assume the negation of the conclusion as `h`. Conclude with `hzg p h hp`. Take `⟨T, hT, hover, hroot⟩` from `hn _ hτ`.

Establish `hsmall` using `hball (y := z) ((dist_pi_lt_iff hη).2 fun i => by`. Rewrite using `[dist_eq_norm]`. Conclude with `hz i)`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`.

Take `⟨c, hc⟩` from `exists_natForm_norm_ge T n hT (fun σ (a : S) => σ (algebraMap A Ω a) - φ a) ε (by`. Introduce `σ hσ`. Establish `hP : σ ∈ PT (Ω` using `Ω) sg := by`. Use extensionality with `k`. Use `RingHom.congr_fun (hover σ hσ) (MvPolynomial.C k)` as an intermediate fact.

Rewrite `this` using `[MvPolynomial.eval₂Hom_C]`. Rewrite using `[← this]`. Express the relevant statement in the definitionally equal form `σ _ = σ (algebraMap A Ω (g (algebraMap K _ k)))`. Rewrite using `[AlgHom.commutes, ← IsScalarTower.algebraMap_apply]`. Take `⟨a, ha, h⟩` from `hcon σ hP`.

Conclude with `⟨⟨a, ha⟩, h⟩)`. Establish `hmon : (minpoly R (b c)).Monic` using `minpoly.monic (Algebra.IsIntegral.isIntegral _)`. Take `⟨r, hr, hrε⟩` from `exists_root_near_of_norm_eval_lt _ (hmon.map (MvPolynomial.eval₂Hom sg z)) (φ (b c)) (ε / 2) (by positivity) (by rw [hmon.natDegree_map]; exact hsmall c)`. Take `⟨σ, hσ, rfl⟩` from `hroot _ r hr`. Use `absurd hrε (not_lt.2 ?_)` and prove the remaining obligations.

Establish `hc'` using `hc σ hσ`. Simplify `hc'` using `only [b, map_sum, map_mul, map_natCast, mul_sub, Finset.sum_sub_distrib]`.
-/
theorem generic_points_dense : (∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D : ℕ) (z₀ : Fin D → ℂ) (ε : ℝ), 0 < ε → ∃ z : Fin D → ℂ, (∀ i, ‖z i - z₀ i‖ < ε) ∧ ∀ p : MvPolynomial (Fin D) K, p ≠ 0 → MvPolynomial.eval₂ sg z p ≠ 0) → ∀ (K A Ω : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra K Ω] [IsScalarTower K A Ω] (sg : K →+* ℂ) (φ : A →+* ℂ), φ.comp (algebraMap K A) = sg → ∀ (S : Finset A) (ε : ℝ), 0 < ε → ∃ P ∈ PT (Ω := Ω) sg, ∀ a ∈ S, ‖P (algebraMap A Ω a) - φ a‖ < ε := by
  intro hgen K A Ω _ _ _ _ _ _ _ _ _ _ _ sg φ hφ S ε hε
  classical
  obtain ⟨D, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg K A
  let R := MvPolynomial (Fin D) K
  let _ : Algebra R A := g.toRingHom.toAlgebra
  have : Module.Finite R A := hfin
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hinj
  have : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.toEquiv.symm
  obtain ⟨n, hn⟩ := exists_embeddings_over_injective R A Ω
  let z₀ : Fin D → ℂ := fun i => φ (g (MvPolynomial.X i))
  have hz₀ : MvPolynomial.eval₂Hom sg z₀ = φ.comp (algebraMap R A) := by
    apply MvPolynomial.ringHom_ext
    · intro k
      change _ = φ (g (algebraMap K _ k))
      rw [AlgHom.commutes, ← hφ]
      simp
    · intro i
      simp only [MvPolynomial.eval₂Hom_X']
      rfl
  let b : (S → Fin (n + 1)) → A := fun c => ∑ a : S, ((c a : ℕ) : A) * (a : A)
  have hev : ∀ᶠ z in nhds z₀, ∀ c, ‖((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z)).eval
      (φ (b c))‖ < (ε / 2) ^ (minpoly R (b c)).natDegree := by
    rw [Filter.eventually_all]
    intro c
    refine ((continuous_eval_map_eval₂Hom sg (minpoly R (b c)) (φ (b c))).norm.tendsto
      z₀).eventually_lt_const ?_
    have h0 : ((minpoly R (b c)).map (MvPolynomial.eval₂Hom sg z₀)).eval (φ (b c)) = 0 := by
      rw [hz₀, Polynomial.eval_map, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def,
        minpoly.aeval, map_zero]
    simp only [h0, norm_zero]
    positivity
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  obtain ⟨z, hz, hzg⟩ := hgen K sg D z₀ η hη
  have hτ : Function.Injective (MvPolynomial.eval₂Hom sg z) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    by_contra h
    exact hzg p h hp
  obtain ⟨T, hT, hover, hroot⟩ := hn _ hτ
  have hsmall := hball (y := z) ((dist_pi_lt_iff hη).2 fun i => by
    rw [dist_eq_norm]; exact hz i)
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_natForm_norm_ge T n hT
    (fun σ (a : S) => σ (algebraMap A Ω a) - φ a) ε (by
      intro σ hσ
      have hP : σ ∈ PT (Ω := Ω) sg := by
        ext k
        have := RingHom.congr_fun (hover σ hσ) (MvPolynomial.C k)
        rw [MvPolynomial.eval₂Hom_C] at this
        rw [← this]
        change σ _ = σ (algebraMap A Ω (g (algebraMap K _ k)))
        rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
      obtain ⟨a, ha, h⟩ := hcon σ hP
      exact ⟨⟨a, ha⟩, h⟩)
  have hmon : (minpoly R (b c)).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral _)
  obtain ⟨r, hr, hrε⟩ := exists_root_near_of_norm_eval_lt _
    (hmon.map (MvPolynomial.eval₂Hom sg z)) (φ (b c)) (ε / 2) (by positivity)
    (by rw [hmon.natDegree_map]; exact hsmall c)
  obtain ⟨σ, hσ, rfl⟩ := hroot _ r hr
  refine absurd hrε (not_lt.2 ?_)
  have hc' := hc σ hσ
  simpa only [b, map_sum, map_mul, map_natCast, mul_sub, Finset.sum_sub_distrib] using hc'

end GlobalTheory
