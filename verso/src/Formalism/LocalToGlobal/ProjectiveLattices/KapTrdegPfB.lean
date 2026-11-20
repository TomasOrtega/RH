import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPfA

namespace Formalism.L2.Pj.TranscendenceDegreeLemmas

open AlgebraicGeometry CategoryTheory

/- English proof (translation)
Establish `hZc : IsClosed Z` using `isClosed_of_mem_irreducibleComponents Z hZ`. Establish `hgen : IsGenericPoint hZ.1.genericPoint Z`. Use `hZ.1.isGenericPoint_genericPoint_closure` as an intermediate fact. Rewrite `this` using `[hZc.closure_eq]`. Then use the resulting hypothesis. Use `⟨⟨(hV.primeIdealOf ⟨_, hx⟩).isPrime, bot_le⟩, fun q hq hle => ?_⟩` and prove the remaining obligations.

Set `y : PrimeSpectrum Γ(X, V)` to `⟨q, hq.1⟩`. Establish `hsp : y ⤳ hV.primeIdealOf ⟨_, hx⟩` using `(PrimeSpectrum.le_iff_specializes _ _).1 hle`. Establish `hsp' : hV.fromSpec y ⤳ hZ.1.genericPoint`. Use `hsp.map hV.fromSpec.continuous` as an intermediate fact. Rewrite `this` using `[hV.fromSpec_primeIdealOf]`. Then use the resulting hypothesis.

Establish `hirr : IsIrreducible (closure {hV.fromSpec y})` using `isIrreducible_singleton.closure`. Establish `hZle : Z ⊆ closure {hV.fromSpec y}`. Rewrite using `[← hgen.def]`. Conclude with `closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp')) isClosed_closure`. Establish `heq : closure {hV.fromSpec y} = Z` using `(hZ.2 hirr hZle).antisymm hZle`.

Establish `hmem : hV.fromSpec y ∈ Z` using `heq ▸ subset_closure rfl`. Establish `hxy : hV.fromSpec y = hZ.1.genericPoint` using `(hsp'.antisymm (hgen.specializes hmem)).eq`. Establish `hy : y = hV.primeIdealOf ⟨_, hx⟩` using `hV.fromSpec.isOpenEmbedding.injective (hxy.trans (hV.fromSpec_primeIdealOf ⟨_, hx⟩).symm)`. Use `congrArg PrimeSpectrum.asIdeal hy` as an intermediate fact. Conclude with `le_of_eq this.symm`.
-/
theorem primeIdealOf_mem_minimalPrimes {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) {Z : Set X}
    (hZ : Z ∈ irreducibleComponents X) (hx : hZ.1.genericPoint ∈ V) :
    (hV.primeIdealOf ⟨_, hx⟩).asIdeal ∈ minimalPrimes Γ(X, V) := by
  have hZc : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
  have hgen : IsGenericPoint hZ.1.genericPoint Z := by
    have := hZ.1.isGenericPoint_genericPoint_closure
    rwa [hZc.closure_eq] at this
  refine ⟨⟨(hV.primeIdealOf ⟨_, hx⟩).isPrime, bot_le⟩, fun q hq hle => ?_⟩
  let y : PrimeSpectrum Γ(X, V) := ⟨q, hq.1⟩
  have hsp : y ⤳ hV.primeIdealOf ⟨_, hx⟩ := (PrimeSpectrum.le_iff_specializes _ _).1 hle
  have hsp' : hV.fromSpec y ⤳ hZ.1.genericPoint := by
    have := hsp.map hV.fromSpec.continuous
    rwa [hV.fromSpec_primeIdealOf] at this
  have hirr : IsIrreducible (closure {hV.fromSpec y}) := isIrreducible_singleton.closure
  have hZle : Z ⊆ closure {hV.fromSpec y} := by
    rw [← hgen.def]
    exact closure_minimal (Set.singleton_subset_iff.2 (specializes_iff_mem_closure.1 hsp')) isClosed_closure
  have heq : closure {hV.fromSpec y} = Z := (hZ.2 hirr hZle).antisymm hZle
  have hmem : hV.fromSpec y ∈ Z := heq ▸ subset_closure rfl
  have hxy : hV.fromSpec y = hZ.1.genericPoint := (hsp'.antisymm (hgen.specializes hmem)).eq
  have hy : y = hV.primeIdealOf ⟨_, hx⟩ :=
    hV.fromSpec.isOpenEmbedding.injective (hxy.trans (hV.fromSpec_primeIdealOf ⟨_, hx⟩).symm)
  have := congrArg PrimeSpectrum.asIdeal hy
  exact le_of_eq this.symm

/- English proof (translation)
Take `⟨U, hU, V, hV, hxV, e, hP⟩` from `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint`. Establish `hUtop : U = ⊤`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Establish `hfx : f hZ.1.genericPoint ∈ U` using `e hxV`. Rewrite using `[Subsingleton.elim y (f hZ.1.genericPoint)]` and apply the resulting hypothesis.

Substitute `hUtop` using the available equality. Set `e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv`. Set `ψ : K →+* Γ(X, V)` to `(f.appLE ⊤ V e).hom.comp (e0 : K →+* _)`. Set `_ : Algebra K Γ(X, V)` to `ψ.toAlgebra`. Establish `hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V)` using `hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)`.

Establish `hmin` using `primeIdealOf_mem_minimalPrimes hV hZ hxV`. Establish `hcore` using `trdeg_residueField_of_minimal (K := K) n (hV.primeIdealOf ⟨_, hxV⟩).asIdeal hmin`. Set `_ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint)` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩`. Establish `hloc` using `hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩`. Set `eL` to `IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)`.

Set `eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint` to `IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv`. Establish `hc1 : CharZero (X.residueField hZ.1.genericPoint)` using `charZero_of_injective_algebraMap (algebraMap K _).injective`. Establish `hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField` using `charZero_of_injective_algebraMap (algebraMap K _).injective`. Establish `t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint)` using `IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm`. Establish `t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField` using `IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm`.

Establish `a1` using `trdeg_add_eq ℚ K (A := X.residueField hZ.1.genericPoint)`. Establish `a2` using `trdeg_add_eq ℚ K (A := (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField)`. Establish `a3` using `(eR.toRatAlgEquiv).trdeg_eq`. Rewrite `a1`, `a2` using `[trdeg_eq_zero (R := ℚ) (A := K), zero_add]`. Rewrite using `[a1, ← a3, ← a2, hcore]`.
-/
theorem trdeg_residueField_genericPoint {K : Type} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    Algebra.trdeg K (X.residueField hZ.1.genericPoint) = n := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hP⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint
  have hUtop : U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hfx : f hZ.1.genericPoint ∈ U := e hxV
    rwa [Subsingleton.elim y (f hZ.1.genericPoint)]
  subst hUtop
  let e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp (e0 : K →+* _)
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) :=
    hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)
  have hmin := primeIdealOf_mem_minimalPrimes hV hZ hxV
  have hcore := trdeg_residueField_of_minimal (K := K) n (hV.primeIdealOf ⟨_, hxV⟩).asIdeal hmin
  let _ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩
  let eL := IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)
  let eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint :=
    IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
  have hc1 : CharZero (X.residueField hZ.1.genericPoint) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint) :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have a1 := trdeg_add_eq ℚ K (A := X.residueField hZ.1.genericPoint)
  have a2 := trdeg_add_eq ℚ K (A := (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField)
  have a3 := (eR.toRatAlgEquiv).trdeg_eq
  rw [trdeg_eq_zero (R := ℚ) (A := K), zero_add] at a1 a2
  rw [a1, ← a3, ← a2, hcore]

/- English proof (translation)
Take `⟨U, hU, V, hV, hxV, e, hP⟩` from `SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint`. Establish `hUtop : U = ⊤`. Use `eq_top_iff.2 fun y _ => ?_` and prove the remaining obligations. Establish `hfx : f hZ.1.genericPoint ∈ U` using `e hxV`. Rewrite using `[Subsingleton.elim y (f hZ.1.genericPoint)]` and apply the resulting hypothesis.

Substitute `hUtop` using the available equality. Set `e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv`. Set `ψ : K →+* Γ(X, V)` to `(f.appLE ⊤ V e).hom.comp (e0 : K →+* _)`. Set `_ : Algebra K Γ(X, V)` to `ψ.toAlgebra`. Establish `hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V)` using `hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)`.

Establish `hmin` using `primeIdealOf_mem_minimalPrimes hV hZ hxV`. Set `_ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint)` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩`. Establish `hloc` using `hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩`. Set `eL` to `IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)`. Set `eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint` to `IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv`.

Establish `hc1 : CharZero (X.residueField hZ.1.genericPoint)` using `charZero_of_injective_algebraMap (algebraMap K _).injective`. Establish `hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField` using `charZero_of_injective_algebraMap (algebraMap K _).injective`. Establish `t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint)` using `IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm`. Establish `t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField` using `IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm`. Establish `f00 : Algebra.IsStandardSmooth K Γ(X, V)` using `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n`.

Establish `f01 : Algebra.FinitePresentation K Γ(X, V)` using `inferInstance`. Establish `f0 : Algebra.EssFiniteType K Γ(X, V)` using `inferInstance`. Establish `f1 : Algebra.EssFiniteType K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField` using `Algebra.EssFiniteType.comp K Γ(X, V) _`. Establish `f2 : Algebra.EssFiniteType ℚ K` using `inferInstance`. Establish `f3 : Algebra.EssFiniteType ℚ (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField` using `Algebra.EssFiniteType.comp ℚ K _`.

Establish `f4 : Algebra.EssFiniteType ℚ (X.residueField hZ.1.genericPoint)` using `(Algebra.EssFiniteType.iff_of_algEquiv eR.toRatAlgEquiv).1 f3`. Establish `f5 : Algebra.EssFiniteType K (X.residueField hZ.1.genericPoint)` using `Algebra.EssFiniteType.of_comp ℚ K _`. Conclude with `IntermediateField.fg_top K _`.
-/
theorem fg_residueField_genericPoint {K : Type} [Field K] [CharZero K] [FiniteDimensional ℚ K]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    {Z : Set X} (hZ : Z ∈ irreducibleComponents X) [Algebra K (X.residueField hZ.1.genericPoint)] :
    (⊤ : IntermediateField K (X.residueField hZ.1.genericPoint)).FG := by
  classical
  obtain ⟨U, hU, V, hV, hxV, e, hP⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := n) (f := f) hZ.1.genericPoint
  have hUtop : U = ⊤ := by
    refine eq_top_iff.2 fun y _ => ?_
    have hfx : f hZ.1.genericPoint ∈ U := e hxV
    rwa [Subsingleton.elim y (f hZ.1.genericPoint)]
  subst hUtop
  let e0 : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  let ψ : K →+* Γ(X, V) := (f.appLE ⊤ V e).hom.comp (e0 : K →+* _)
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have hsm : Algebra.IsStandardSmoothOfRelativeDimension n K Γ(X, V) :=
    hP.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv e0)
  have hmin := primeIdealOf_mem_minimalPrimes hV hZ hxV
  let _ : Algebra Γ(X, V) (X.presheaf.stalk hZ.1.genericPoint) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hZ.1.genericPoint, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨hZ.1.genericPoint, hxV⟩
  let eL := IsLocalization.algEquiv (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.primeCompl
    (Localization.AtPrime (hV.primeIdealOf ⟨_, hxV⟩).asIdeal) (X.presheaf.stalk hZ.1.genericPoint)
  let eR : (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField ≃+* X.residueField hZ.1.genericPoint :=
    IsLocalRing.ResidueField.mapEquiv eL.toRingEquiv
  have hc1 : CharZero (X.residueField hZ.1.genericPoint) :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have hc2 : CharZero (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    charZero_of_injective_algebraMap (algebraMap K _).injective
  have t1 : IsScalarTower ℚ K (X.residueField hZ.1.genericPoint) :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have t2 : IsScalarTower ℚ K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun q => ((algebraMap K _).map_rat_algebraMap q).symm
  have f00 : Algebra.IsStandardSmooth K Γ(X, V) := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n
  have f01 : Algebra.FinitePresentation K Γ(X, V) := inferInstance
  have f0 : Algebra.EssFiniteType K Γ(X, V) := inferInstance
  have f1 : Algebra.EssFiniteType K (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp K Γ(X, V) _
  have f2 : Algebra.EssFiniteType ℚ K := inferInstance
  have f3 : Algebra.EssFiniteType ℚ (hV.primeIdealOf ⟨_, hxV⟩).asIdeal.ResidueField :=
    Algebra.EssFiniteType.comp ℚ K _
  have f4 : Algebra.EssFiniteType ℚ (X.residueField hZ.1.genericPoint) :=
    (Algebra.EssFiniteType.iff_of_algEquiv eR.toRatAlgEquiv).1 f3
  have f5 : Algebra.EssFiniteType K (X.residueField hZ.1.genericPoint) := Algebra.EssFiniteType.of_comp ℚ K _
  exact IntermediateField.fg_top K _

end Formalism.L2.Pj.TranscendenceDegreeLemmas
