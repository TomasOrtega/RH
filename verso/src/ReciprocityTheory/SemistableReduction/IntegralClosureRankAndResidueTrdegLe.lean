import Mathlib
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom

namespace ReciprocityTheory.MultiplicativeHeights

/- English proof (translation)
Use `set C := integralClosure O L`. Use `haveI hD : IsDedekindDomain C := integralClosure.isDedekindDomain O F L`. Use `haveI hFin : Module.Finite O C := IsIntegralClosure.finite O F L C`. Use `haveI : Module.IsTorsionFree O L := by`. Rewrite using `[Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O F L]`.

Conclude with `(algebraMap F L).injective.comp (IsFractionRing.injective O F)`. Use `haveI : Module.IsTorsionFree O C := inferInstance`. Use `haveI hFr : Module.Free O C := Module.free_of_finite_type_torsion_free'`. Use `haveI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension O F L C`. Use `set m := IsLocalRing.maximalIdeal O`.

Establish `hm : m ≠ ⊥` using `IsDiscreteValuationRing.not_a_field O`. Establish `key : ∀ Q : Ideal C, Q.IsMaximal ↔ Q ∈ IsDedekindDomain.primesOverFinset m C`. Introduce `Q`. Rewrite using `[IsDedekindDomain.mem_primesOverFinset_iff hm C]`. Prove the components needed by the constructor for the conclusion.

Introduce `hQ`. Establish `hu : (Q.under O).IsMaximal` using `Ideal.IsMaximal.under O Q`. Use `⟨hQ.isPrime, ⟨?_⟩⟩` and prove the remaining obligations. Conclude with `(IsLocalRing.eq_maximalIdeal hu).symm`. Introduce and unpack `⟨hP, hl⟩`.

Use `hP.isMaximal ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Apply `hm` to reduce the goal to its premises. Rewrite using `[hl.over]`. Conclude with `Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O C)`.

Use `⟨hD, hFin, hFr, IsIntegralClosure.rank O F L C, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(IsDedekindDomain.primesOverFinset m C).finite_toSet.subset fun Q hQ => (key Q).1 hQ`. Rewrite using `[← Ideal.sum_ramification_inertia C F L hm]`. Rewrite using `[← finsum_comp_equiv (Equiv.subtypeEquivRight key).symm, finsum_eq_sum_of_fintype, ← Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset m C)]`. Use `Finset.sum_congr rfl fun P _ => ?_` and prove the remaining obligations.

Establish `hP` using `P.2`. Rewrite `hP` using `[IsDedekindDomain.mem_primesOverFinset_iff hm C]`. Use `haveI := hP.1`. Use `haveI := hP.2`. Use `haveI : P.1.IsMaximal := ((key P.1).2 P.2)`.

Simplify using `only [Equiv.subtypeEquivRight_symm_apply_coe]`. Rewrite using `[Ideal.ramificationIdx_eq_ramificationIdx' m P.1 hm, Ideal.inertiaDeg_eq_inertiaDeg' m P.1]`.
-/
theorem integralClosureRank (O F L : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O F] [IsFractionRing O F] [Field L] [Algebra F L] [FiniteDimensional F L]
    [Algebra.IsSeparable F L] [Algebra O L] [IsScalarTower O F L] :
    IsDedekindDomain (integralClosure O L) ∧ Module.Finite O (integralClosure O L) ∧
      Module.Free O (integralClosure O L) ∧
      Module.finrank O (integralClosure O L) = Module.finrank F L ∧
      {Q : Ideal (integralClosure O L) | Q.IsMaximal}.Finite ∧
      ∑ᶠ Q : {Q : Ideal (integralClosure O L) // Q.IsMaximal},
          Q.1.ramificationIdx O * Q.1.inertiaDeg O = Module.finrank F L := by
  set C := integralClosure O L
  haveI hD : IsDedekindDomain C := integralClosure.isDedekindDomain O F L
  haveI hFin : Module.Finite O C := IsIntegralClosure.finite O F L C
  haveI : Module.IsTorsionFree O L := by
    rw [Module.isTorsionFree_iff_algebraMap_injective, IsScalarTower.algebraMap_eq O F L]
    exact (algebraMap F L).injective.comp (IsFractionRing.injective O F)
  haveI : Module.IsTorsionFree O C := inferInstance
  haveI hFr : Module.Free O C := Module.free_of_finite_type_torsion_free'
  haveI : IsFractionRing C L := IsIntegralClosure.isFractionRing_of_finite_extension O F L C
  set m := IsLocalRing.maximalIdeal O
  have hm : m ≠ ⊥ := IsDiscreteValuationRing.not_a_field O
  have key : ∀ Q : Ideal C, Q.IsMaximal ↔ Q ∈ IsDedekindDomain.primesOverFinset m C := by
    intro Q
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C]
    constructor
    · intro hQ
      have hu : (Q.under O).IsMaximal := Ideal.IsMaximal.under O Q
      refine ⟨hQ.isPrime, ⟨?_⟩⟩
      exact (IsLocalRing.eq_maximalIdeal hu).symm
    · rintro ⟨hP, hl⟩
      refine hP.isMaximal ?_
      rintro rfl
      apply hm
      rw [hl.over]
      exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective O C)
  refine ⟨hD, hFin, hFr, IsIntegralClosure.rank O F L C, ?_, ?_⟩
  · exact (IsDedekindDomain.primesOverFinset m C).finite_toSet.subset fun Q hQ => (key Q).1 hQ
  · rw [← Ideal.sum_ramification_inertia C F L hm]
    rw [← finsum_comp_equiv (Equiv.subtypeEquivRight key).symm, finsum_eq_sum_of_fintype,
      ← Finset.sum_coe_sort (IsDedekindDomain.primesOverFinset m C)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.2
    rw [IsDedekindDomain.mem_primesOverFinset_iff hm C] at hP
    haveI := hP.1
    haveI := hP.2
    haveI : P.1.IsMaximal := ((key P.1).2 P.2)
    simp only [Equiv.subtypeEquivRight_symm_apply_coe]
    rw [Ideal.ramificationIdx_eq_ramificationIdx' m P.1 hm, Ideal.inertiaDeg_eq_inertiaDeg' m P.1]

open MvPolynomial

/- English proof (translation)
Use `letI := residueAlgebra V (algebraMap F₁ F₂)`. Rewrite `hx`, the goal using `[algebraicIndependent_iff]`. Introduce `p hp`. Assume the negation of the conclusion as `hne`. Establish `hS : p.support.Nonempty`.

Rewrite using `[Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]` and apply the resulting hypothesis. Take `⟨m₀, hm₀, hmax⟩` from `p.support.exists_max_image (fun m => (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)) hS`. Establish `hc : p.coeff m₀ ≠ 0` using `MvPolynomial.mem_support_iff.1 hm₀`. Establish `hvc : (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) ≠ 0` using `(Valuation.ne_zero_iff _).2 hc`. Establish `hle : ∀ m, (p.coeff m₀)⁻¹ * p.coeff m ∈ V.comap (algebraMap F₁ F₂)`.

Introduce `m`. Rewrite using `[← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]`. Distinguish the cases in `hm : m ∈ p.support`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hmax m hm`.

Use `_ = 1 := inv_mul_cancel₀ hvc`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hm]`. Simplify using the standard rewrite rules. Establish `hpp : MvPolynomial.C (p.coeff m₀)⁻¹ * p ∈ Set.range (MvPolynomial.map (V.comap (algebraMap F₁ F₂)).subtype)`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`.

Introduce `a ha`. Take `⟨m, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.1 ha`. Conclude with `⟨⟨_, hle m⟩, by simp [MvPolynomial.coeff_C_mul]⟩`. Take `⟨qV, hqV⟩` from `hpp`. Establish `hcoeff : qV.coeff m₀ = 1`.

Establish `e` using `congrArg (MvPolynomial.coeff m₀) hqV`. Rewrite `e` using `[MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc]`. Conclude with `Subtype.ext e`. Establish `h0 : MvPolynomial.eval₂ (comapInclusion V (algebraMap F₁ F₂)) y qV = 0`. Apply `Subtype.ext` to reduce the goal to its premises.

Establish `e1 : MvPolynomial.aeval (fun i => ((y i : V) : F₂)) (MvPolynomial.C (p.coeff m₀)⁻¹ * p) = 0`. Rewrite using `[map_mul, hp, mul_zero]`. Rewrite `e1` using `[MvPolynomial.aeval_def, ← hqV, MvPolynomial.eval₂_map]`. Establish `e2` using `MvPolynomial.eval₂_comp_left V.subtype (comapInclusion V (algebraMap F₁ F₂)) y qV`. Establish `e3 : V.subtype.comp (comapInclusion V (algebraMap F₁ F₂)) = (algebraMap F₁ F₂).comp (V.comap (algebraMap F₁ F₂)).subtype` using `RingHom.ext fun _ => rfl`.

Rewrite `e2` using `[e3]`. Conclude with `e2.trans e1`. Establish `h1 : MvPolynomial.aeval (fun i => IsLocalRing.residue V (y i)) (MvPolynomial.map (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) qV) = 0`. Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_map]`. Establish `e4` using `MvPolynomial.eval₂_comp_left (IsLocalRing.residue V) (comapInclusion V (algebraMap F₁ F₂)) y qV`.

Rewrite `e4` using `[h0, map_zero]`. Establish `e5 : (algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂))) (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) = (IsLocalRing.residue V).comp (comapInclusion V (algebraMap F₁ F₂))` using `RingHom.ext fun r => IsLocalRing.ResidueField.map_residue _ r`. Rewrite using `[e5]`. Conclude with `e4.symm`. Establish `e6` using `congrArg (MvPolynomial.coeff m₀) (hx _ h1)`.

Rewrite `e6` using `[MvPolynomial.coeff_map, hcoeff, map_one, MvPolynomial.coeff_zero]`. Conclude with `one_ne_zero e6`.
-/
theorem algebraicIndependent_of_residue_lift {F₁ F₂ : Type} [Field F₁] [Field F₂] [Algebra F₁ F₂]
    (V : ValuationSubring F₂) {ι : Type*} (y : ι → V)
    (hx : letI := residueAlgebra V (algebraMap F₁ F₂)
      AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (fun i => IsLocalRing.residue V (y i))) :
    AlgebraicIndependent F₁ (fun i => ((y i : V) : F₂)) := by
  classical
  letI := residueAlgebra V (algebraMap F₁ F₂)
  rw [algebraicIndependent_iff] at hx ⊢
  intro p hp
  by_contra hne
  have hS : p.support.Nonempty := by
    rwa [Finset.nonempty_iff_ne_empty, Ne, MvPolynomial.support_eq_empty]
  obtain ⟨m₀, hm₀, hmax⟩ := p.support.exists_max_image
    (fun m => (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)) hS
  have hc : p.coeff m₀ ≠ 0 := MvPolynomial.mem_support_iff.1 hm₀
  have hvc : (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hc

  have hle : ∀ m, (p.coeff m₀)⁻¹ * p.coeff m ∈ V.comap (algebraMap F₁ F₂) := by
    intro m
    rw [← ValuationSubring.valuation_le_one_iff, map_mul, map_inv₀]
    by_cases hm : m ∈ p.support
    · calc ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m)
          ≤ ((V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀))⁻¹ *
            (V.comap (algebraMap F₁ F₂)).valuation (p.coeff m₀) := by
            gcongr
            exact hmax m hm
        _ = 1 := inv_mul_cancel₀ hvc
    · rw [MvPolynomial.notMem_support_iff.1 hm]
      simp
  have hpp : MvPolynomial.C (p.coeff m₀)⁻¹ * p ∈
      Set.range (MvPolynomial.map (V.comap (algebraMap F₁ F₂)).subtype) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro a ha
    obtain ⟨m, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 ha
    exact ⟨⟨_, hle m⟩, by simp [MvPolynomial.coeff_C_mul]⟩
  obtain ⟨qV, hqV⟩ := hpp
  have hcoeff : qV.coeff m₀ = 1 := by
    have e := congrArg (MvPolynomial.coeff m₀) hqV
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_C_mul, inv_mul_cancel₀ hc] at e
    exact Subtype.ext e
  have h0 : MvPolynomial.eval₂ (comapInclusion V (algebraMap F₁ F₂)) y qV = 0 := by
    apply Subtype.ext
    have e1 : MvPolynomial.aeval (fun i => ((y i : V) : F₂))
        (MvPolynomial.C (p.coeff m₀)⁻¹ * p) = 0 := by
      rw [map_mul, hp, mul_zero]
    rw [MvPolynomial.aeval_def, ← hqV, MvPolynomial.eval₂_map] at e1
    have e2 := MvPolynomial.eval₂_comp_left V.subtype (comapInclusion V (algebraMap F₁ F₂)) y qV
    have e3 : V.subtype.comp (comapInclusion V (algebraMap F₁ F₂)) =
        (algebraMap F₁ F₂).comp (V.comap (algebraMap F₁ F₂)).subtype := RingHom.ext fun _ => rfl
    rw [e3] at e2
    exact e2.trans e1

  have h1 : MvPolynomial.aeval (fun i => IsLocalRing.residue V (y i))
      (MvPolynomial.map (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) qV) = 0 := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_map]
    have e4 := MvPolynomial.eval₂_comp_left (IsLocalRing.residue V)
      (comapInclusion V (algebraMap F₁ F₂)) y qV
    rw [h0, map_zero] at e4
    have e5 : (algebraMap (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
        (IsLocalRing.ResidueField V)).comp (IsLocalRing.residue (V.comap (algebraMap F₁ F₂))) =
        (IsLocalRing.residue V).comp (comapInclusion V (algebraMap F₁ F₂)) :=
      RingHom.ext fun r => IsLocalRing.ResidueField.map_residue _ r
    rw [e5]
    exact e4.symm
  have e6 := congrArg (MvPolynomial.coeff m₀) (hx _ h1)
  rw [MvPolynomial.coeff_map, hcoeff, map_one, MvPolynomial.coeff_zero] at e6
  exact one_ne_zero e6

/- English proof (translation)
Introduce `F₁ F₂ _ _ _ V`. Use `letI := residueAlgebra V (algebraMap F₁ F₂)`. Unfold `Algebra.trdeg`. Use `ciSup_le' fun s => ?_` and prove the remaining obligations. Establish `hy : ∀ a : s.1, ∃ v : V, IsLocalRing.residue V v = a` using `fun a => IsLocalRing.residue_surjective (a : IsLocalRing.ResidueField V)`.

Use `choose y hy using hy`. Establish `hs : AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂))) (fun a => IsLocalRing.residue V (y a))`. Establish `: (fun a => IsLocalRing.residue V (y a)) = ((↑) : s.1 → IsLocalRing.ResidueField V)`. Use function extensionality and compare the values at `hy`. Rewrite using `[this]`.

Conclude with `s.2`. Conclude with `(algebraicIndependent_of_residue_lift V y hs).cardinalMk_le_trdeg`.
-/
theorem residueTrdegLe : TRStatement := by
  intro F₁ F₂ _ _ _ V
  letI := residueAlgebra V (algebraMap F₁ F₂)
  unfold Algebra.trdeg
  refine ciSup_le' fun s => ?_
  have hy : ∀ a : s.1, ∃ v : V, IsLocalRing.residue V v = a :=
    fun a => IsLocalRing.residue_surjective (a : IsLocalRing.ResidueField V)
  choose y hy using hy
  have hs : AlgebraicIndependent (IsLocalRing.ResidueField (V.comap (algebraMap F₁ F₂)))
      (fun a => IsLocalRing.residue V (y a)) := by
    have : (fun a => IsLocalRing.residue V (y a)) = ((↑) : s.1 → IsLocalRing.ResidueField V) :=
      funext hy
    rw [this]
    exact s.2
  exact (algebraicIndependent_of_residue_lift V y hs).cardinalMk_le_trdeg

/- English proof (translation)
Assemble the required witnesses or components as `⟨by intro O F L; intros; exact integralClosureRank O F L, residueTrdegLe⟩`.
-/
theorem integralClosureRank_and_residueTrdegLe : DedekindRankStatement ∧ TRStatement :=
  ⟨by intro O F L; intros; exact integralClosureRank O F L, residueTrdegLe⟩

end ReciprocityTheory.MultiplicativeHeights
