import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimConeImageOfBirationalLinearSystem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeDegreeGrowthChowFormIntegrality
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.PIntDomainDim

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHt

namespace ModelDimension.ModelDim

/- English proof (translation)
Establish `: IsDomain A` using `hφ.isDomain φ`. Establish `: CharZero A` using `φ.charZero`. Set `_ : Algebra A Ω` to `φ.toAlgebra`. Establish `: FaithfulSMul A Ω` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hφ`. Establish `: IsFractionRing A Ω` using `IsFractionRing.of_field _ _ hfr`.

Establish `: Algebra.IsAlgebraic A Ω` using `IsLocalization.isAlgebraic Ω (nonZeroDivisors A)`. Establish `h1` using `GroundTheory.Heights₂.Heights.IntDomainDim.proof A (algebraMap ℤ A).injective_int`. Rewrite using `[h1, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top ℤ A Ω, hd, Cardinal.toENat_nat]`. Use `norm_cast`.
-/
theorem ringKrullDim_eq {A Ω : Type} [CommRing A] [Field Ω] [CharZero Ω] (φ : A →+* Ω)
    (hφ : Function.Injective φ) (hfr : ∀ x : Ω, ∃ a b : A, x = φ a / φ b) (hft : Algebra.FiniteType ℤ A) {d : ℕ}
    (hd : Algebra.trdeg ℤ Ω = d) : ringKrullDim A = (d + 1 : ℕ) := by
  have : IsDomain A := hφ.isDomain φ
  have : CharZero A := φ.charZero
  let _ : Algebra A Ω := φ.toAlgebra
  have : FaithfulSMul A Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : IsFractionRing A Ω := IsFractionRing.of_field _ _ hfr
  have : Algebra.IsAlgebraic A Ω := IsLocalization.isAlgebraic Ω (nonZeroDivisors A)
  have h1 := GroundTheory.Heights₂.Heights.IntDomainDim.proof A (algebraMap ℤ A).injective_int
  rw [h1, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top ℤ A Ω, hd, Cardinal.toENat_nat]
  norm_cast

/- English proof (translation)
Use `M.lft` as an intermediate fact. Establish `: LocallyOfFiniteType (spMap (Int.castRingHom o))` using `(HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 ho)`. Set `t : M.Z ⟶ Sp ℤ` to `M.s ≫ spMap (Int.castRingHom o)`. Establish `ht : LocallyOfFiniteType t` using `inferInstance`. Establish `key (U : M.Z.Opens) (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) : topologicalKrullDim (U : Set M.Z) = (d + 1 : ℕ)`.

Establish `h1 : (t.appLE ⊤ U le_top).hom.FiniteType` using `HasRingHomProperty.appLE @LocallyOfFiniteType t ht ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _`. Establish `e : (t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom = algebraMap ℤ Γ(M.Z, U)` using `RingHom.ext_int _ _`. Rewrite `h1` using `[← RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of ℤ)).inv, e, RingHom.finiteType_algebraMap]`. Use `((GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec).trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(M.Z, U)))).trans ?_` and prove the remaining obligations. Use `ringKrullDim_eq (M.res U hne) (M.res_injective U hne) (fun x => ?_) h1 hd` and prove the remaining obligations.

Take `⟨a, b, -, h⟩` from `GlobalTheory.ZH.RatModel.exists_eq_div hU hne x`. Conclude with `⟨a, b, by rw [M.res_apply, M.res_apply]; exact h⟩`. Apply `le_antisymm` to reduce the goal to its premises. Use `GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_` and prove the remaining obligations. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial`.

Conclude with `⟨U, U.isOpen, hx, (key U hU ⟨x, hx⟩).le⟩`. Take `⟨U, hU, hx, -⟩` from `exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint M.Z) trivial`. Rewrite using `[← key U hU ⟨_, hx⟩]`. Conclude with `topologicalKrullDim_subspace_le _ _`.
-/
theorem topologicalKrullDim_model {o Ω : Type} [CommRing o] [Field Ω] [CharZero Ω] [Algebra o Ω]
    (ho : Algebra.FiniteType ℤ o) (M : GlobalTheory.ZH.RatModel o Ω) {d : ℕ} (hd : Algebra.trdeg ℤ Ω = d) :
    topologicalKrullDim M.Z = (d + 1 : ℕ) := by
  have := M.lft
  have : LocallyOfFiniteType (spMap (Int.castRingHom o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 ho)
  let t : M.Z ⟶ Sp ℤ := M.s ≫ spMap (Int.castRingHom o)
  have ht : LocallyOfFiniteType t := inferInstance
  have key (U : M.Z.Opens) (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty) :
      topologicalKrullDim (U : Set M.Z) = (d + 1 : ℕ) := by
    have h1 : (t.appLE ⊤ U le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType t ht ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ _
    have e : (t.appLE ⊤ U le_top).hom.comp (Scheme.ΓSpecIso (.of ℤ)).inv.hom =
      algebraMap ℤ Γ(M.Z, U) := RingHom.ext_int _ _
    rw [← RingHom.finiteType_respectsIso.cancel_left_isIso (Scheme.ΓSpecIso (.of ℤ)).inv, e,
      RingHom.finiteType_algebraMap] at h1
    refine ((GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding
      hU.range_fromSpec).trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(M.Z, U)))).trans ?_
    refine ringKrullDim_eq (M.res U hne) (M.res_injective U hne) (fun x => ?_) h1 hd
    obtain ⟨a, b, -, h⟩ := GlobalTheory.ZH.RatModel.exists_eq_div hU hne x
    exact ⟨a, b, by rw [M.res_apply, M.res_apply]; exact h⟩
  apply le_antisymm
  · refine GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_
    obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
    exact ⟨U, U.isOpen, hx, (key U hU ⟨x, hx⟩).le⟩
  · obtain ⟨U, hU, hx, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := genericPoint M.Z) trivial
    rw [← key U hU ⟨_, hx⟩]
    exact topologicalKrullDim_subspace_le _ _

/- English proof (translation)
Take `⟨N, b, f, hf⟩` from `(imageDeg_pos_iff ev d).1 hd`. Use `set y : Fin N → Ω := fun j => ev (b j) with hy`. Establish `hy0 : y ≠ 0` using `fun h => hg.1 (b.ext fun j => congrFun h j)`. Establish `hgen : Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤`. Take `⟨j, hj⟩` from `Function.ne_iff.1 hy0`.

Establish `hj' : y j ≠ 0` using `hj`. Use `set F := Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) with hF`. Establish `h1 : ∀ v, ev v / y j ∈ F` using `fun v => by`. Rewrite using `[← b.sum_repr v, map_sum, Finset.sum_div]`. Use `sum_mem fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[map_smul, Algebra.smul_def, mul_div_assoc]`. Conclude with `mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩))`. Establish `h2` using `congrArg IntermediateField.toSubfield hg.2`. Rewrite `h2` using `[GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield]`. Use `top_unique (h2 ▸ Subfield.closure_le.2 ?_)` and prove the remaining obligations.

Introduce and unpack `_ (⟨c, rfl⟩ | ⟨v, w, rfl⟩)`. Conclude with `Subfield.subset_closure (Or.inl ⟨_, rfl⟩)`. Rewrite using `[← div_div_div_cancel_right₀ hj']`. Conclude with `div_mem (h1 v) (h1 w)`. Use `isPrime_coneIdeal (K := K) y` as an intermediate fact.

Establish `hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = (d + 1 : ℕ)` using `GlobalTheory.ConeDeg.ringKrullDim_of_isChowFormInt (fun g hg n => homogeneousComponent_mem_of_mem (isHomogeneous_coneIdeal y) hg n) hf`. Take `⟨e, he1, he2⟩` from `GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq K (MvPolynomial (Fin N) K ⧸ coneIdeal K y)`. Take `rfl : e = d + 1` from `by exact_mod_cast he1.symm.trans hdim`. Set `φ` to `Ideal.kerLiftAlg (coneMap K y)`. Establish `hφ : Function.Injective φ` using `Ideal.kerLiftAlg_injective _`.

Set `A` to `φ.range`. Set `e` to `AlgEquiv.ofInjective φ hφ`. Establish `hQA : Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = Algebra.trdeg K A` using `le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective) (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)`. Establish `hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A` using `fun i => by`. Use `AlgHom.mem_range_self φ (Ideal.Quotient.mk _ (X i))` as an intermediate fact.

Rewrite `this` using `[Ideal.kerLiftAlg_mk]`. Simplify using `only [coneMap, aeval_X] at this`. Conclude with `this`. Use `GlobalTheory.Adelic.ConeDim.isAlgebraic_of_closure_eq_top y hy0 hgen A hXy` as an intermediate fact. Establish `: FaithfulSMul K A` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)`.

Establish `: FaithfulSMul A (Polynomial Ω)` using `(faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective`. Rewrite `he2` using `[hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top K A (Polynomial Ω), ← trdeg_add_eq K Ω (A := Polynomial Ω), Polynomial.trdeg_of_isDomain, Nat.cast_add, Nat.cast_one]`. Conclude with `(Cardinal.add_one_inj).1 he2`.
-/
theorem trdeg_eq {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]
    (ev : V →ₗ[K] Ω) (hg : GlobalTheory.DegVal.GenRatios ev) {d : ℕ} (hd : 0 < imageDeg ev d) :
    Algebra.trdeg K Ω = d := by
  obtain ⟨N, b, f, hf⟩ := (imageDeg_pos_iff ev d).1 hd
  set y : Fin N → Ω := fun j => ev (b j) with hy
  have hy0 : y ≠ 0 := fun h => hg.1 (b.ext fun j => congrFun h j)
  have hgen : Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) = ⊤ := by
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hy0
    have hj' : y j ≠ 0 := hj
    set F := Subfield.closure (Set.range (algebraMap K Ω) ∪ {r | ∃ i j, r = y i / y j}) with hF
    have h1 : ∀ v, ev v / y j ∈ F := fun v => by
      rw [← b.sum_repr v, map_sum, Finset.sum_div]
      refine sum_mem fun i _ => ?_
      rw [map_smul, Algebra.smul_def, mul_div_assoc]
      exact mul_mem (Subfield.subset_closure (Or.inl ⟨_, rfl⟩)) (Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩))
    have h2 := congrArg IntermediateField.toSubfield hg.2
    rw [GlobalTheory.DegVal.ratioField, IntermediateField.adjoin_toSubfield, IntermediateField.top_toSubfield] at h2
    refine top_unique (h2 ▸ Subfield.closure_le.2 ?_)
    rintro _ (⟨c, rfl⟩ | ⟨v, w, rfl⟩)
    · exact Subfield.subset_closure (Or.inl ⟨_, rfl⟩)
    · rw [← div_div_div_cancel_right₀ hj']
      exact div_mem (h1 v) (h1 w)
  have := isPrime_coneIdeal (K := K) y
  have hdim : ringKrullDim (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = (d + 1 : ℕ) :=
    GlobalTheory.ConeDeg.ringKrullDim_of_isChowFormInt
      (fun g hg n => homogeneousComponent_mem_of_mem (isHomogeneous_coneIdeal y) hg n) hf
  obtain ⟨e, he1, he2⟩ := GlobalTheory.exists_ringKrullDim_eq_and_trdeg_eq K (MvPolynomial (Fin N) K ⧸ coneIdeal K y)
  obtain rfl : e = d + 1 := by exact_mod_cast he1.symm.trans hdim
  let φ := Ideal.kerLiftAlg (coneMap K y)
  have hφ : Function.Injective φ := Ideal.kerLiftAlg_injective _
  let A := φ.range
  let e := AlgEquiv.ofInjective φ hφ
  have hQA : Algebra.trdeg K (MvPolynomial (Fin N) K ⧸ coneIdeal K y) = Algebra.trdeg K A :=
    le_antisymm (trdeg_le_of_injective e.toAlgHom e.injective)
      (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
  have hXy : ∀ i, Polynomial.X * Polynomial.C (y i) ∈ A := fun i => by
    have := AlgHom.mem_range_self φ (Ideal.Quotient.mk _ (X i))
    rw [Ideal.kerLiftAlg_mk] at this
    simp only [coneMap, aeval_X] at this
    exact this
  have := GlobalTheory.Adelic.ConeDim.isAlgebraic_of_closure_eq_top y hy0 hgen A hXy
  have : FaithfulSMul K A := (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  have : FaithfulSMul A (Polynomial Ω) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  rw [hQA, ← GlobalTheory.trdeg_eq_of_isAlgebraic_top K A (Polynomial Ω), ← trdeg_add_eq K Ω (A := Polynomial Ω),
    Polynomial.trdeg_of_isDomain, Nat.cast_add, Nat.cast_one] at he2
  exact (Cardinal.add_one_inj).1 he2

end ModelDimension.ModelDim
