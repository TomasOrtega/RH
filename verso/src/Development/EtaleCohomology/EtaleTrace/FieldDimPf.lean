import Development.EtaleCohomology.EtaleTrace.LCoverCut

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.EtaleTrace.Cov

/- English proof (translation)
Establish `: Algebra.FormallyEtale R K` using `Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)`. Establish `: Algebra.IsStandardSmooth k R` using `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d`. Establish `: Module.Free R Ω[R⁄k]` using `Algebra.IsStandardSmooth.free_kaehlerDifferential`. Establish `hr : Module.rank R Ω[R⁄k] = d` using `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d`. Establish `hf : Module.finrank R Ω[R⁄k] = d` using `Module.finrank_eq_of_rank_eq hr`.

Rewrite using `[← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K).finrank_eq, Module.finrank_baseChange, hf]`.
-/
theorem finrank_frac_of_stdSmooth (k R K : Type) [Field k] [CommRing R] [IsDomain R] [Field K]
    [Algebra k R] [Algebra R K] [Algebra k K] [IsScalarTower k R K] [IsFractionRing R K] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d k R] :
    Module.finrank K Ω[K⁄k] = d := by
  have : Algebra.FormallyEtale R K := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors R)
  have : Algebra.IsStandardSmooth k R := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth d
  have : Module.Free R Ω[R⁄k] := Algebra.IsStandardSmooth.free_kaehlerDifferential
  have hr : Module.rank R Ω[R⁄k] = d := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential d
  have hf : Module.finrank R Ω[R⁄k] = d := Module.finrank_eq_of_rank_eq hr
  rw [← (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k R K).finrank_eq, Module.finrank_baseChange, hf]

/- English proof (translation)
Introduce `k _ d X _ p hp`. Use `letI := (kHom p).toAlgebra`. Take `⟨U, hU, V, hV, hx, e, hf⟩` from `hp.exists_isStandardSmoothOfRelativeDimension (genericPoint X)`. Establish `hUtop : U = ⊤`. Establish `hs : Subsingleton (PrimeSpectrum k)` using `inferInstance`.

Use extensionality with `y`. Simplify using `only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]`. Establish `hy : p.base (genericPoint X) ∈ U` using `e hx`. Conclude with `(show y = p.base (genericPoint X) from hs.elim _ _) ▸ hy`. Substitute `hUtop` using the available equality.

Establish `: Nonempty V` using `⟨⟨_, hx⟩⟩`. Set `ψ : CommRingCat.of k ⟶ Γ(X, V)` to `(Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e`. Establish `hψ : ψ.hom.IsStandardSmoothOfRelativeDimension d`. Use `hf.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)` as an intermediate fact. Conclude with `this`.

Use `letI : Algebra k Γ(X, V) := ψ.hom.toAlgebra`. Use `haveI : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, V) := hψ`. Use `haveI : IsScalarTower k Γ(X, V) X.functionField := by`. Apply `IsScalarTower.of_algebraMap_eq'` to reduce the goal to its premises. Use extensionality with `c`.

Establish `key : Scheme.Hom.appTop p ≫ X.presheaf.germ ⊤ (genericPoint X) trivial = Scheme.Hom.appLE p ⊤ V e ≫ X.germToFunctionField V`. Rewrite using `[Scheme.Hom.appLE, Category.assoc]`. Conclude with `(congrArg (Scheme.Hom.app p ⊤ ≫ ·) (X.presheaf.germ_res (homOfLE le_top) (genericPoint X) hx)).symm`. Simplify using `only [RingHom.algebraMap_toAlgebra, kHom, ψ]`. Establish `H : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e) ≫ X.germToFunctionField V`.

Rewrite using `[Category.assoc, ← key]`. Conclude with `congrArg (fun f => CommRingCat.Hom.hom f c) H`. Use `haveI := functionField_isFractionRing_of_isAffineOpen X V hV`. Conclude with `finrank_frac_of_stdSmooth k Γ(X, V) X.functionField d`.
-/
theorem FieldDim_of : FieldDim := by
  intro k _ d X _ p hp
  letI := (kHom p).toAlgebra
  obtain ⟨U, hU, V, hV, hx, e, hf⟩ := hp.exists_isStandardSmoothOfRelativeDimension (genericPoint X)
  have hUtop : U = ⊤ := by
    have hs : Subsingleton (PrimeSpectrum k) := inferInstance
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have hy : p.base (genericPoint X) ∈ U := e hx
    exact (show y = p.base (genericPoint X) from hs.elim _ _) ▸ hy
  subst hUtop
  have : Nonempty V := ⟨⟨_, hx⟩⟩
  let ψ : CommRingCat.of k ⟶ Γ(X, V) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e
  have hψ : ψ.hom.IsStandardSmoothOfRelativeDimension d := by
    have := hf.comp (RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact this
  letI : Algebra k Γ(X, V) := ψ.hom.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension d k Γ(X, V) := hψ
  haveI : IsScalarTower k Γ(X, V) X.functionField := by
    apply IsScalarTower.of_algebraMap_eq'
    ext c
    have key : Scheme.Hom.appTop p ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        Scheme.Hom.appLE p ⊤ V e ≫ X.germToFunctionField V := by
      rw [Scheme.Hom.appLE, Category.assoc]
      exact (congrArg (Scheme.Hom.app p ⊤ ≫ ·) (X.presheaf.germ_res (homOfLE le_top) (genericPoint X) hx)).symm
    simp only [RingHom.algebraMap_toAlgebra, kHom, ψ]
    have H : (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial =
        ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ V e) ≫ X.germToFunctionField V := by
      rw [Category.assoc, ← key]
    exact congrArg (fun f => CommRingCat.Hom.hom f c) H
  haveI := functionField_isFractionRing_of_isAffineOpen X V hV
  exact finrank_frac_of_stdSmooth k Γ(X, V) X.functionField d

end LateralTheory.EtaleTrace.Cov
