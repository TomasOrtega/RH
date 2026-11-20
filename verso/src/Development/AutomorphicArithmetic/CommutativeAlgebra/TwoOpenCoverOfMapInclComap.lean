import Development.AutomorphicArithmetic.BlowupCategories.SpanScale
import Development.AutomorphicArithmetic.BlowupCategories.AffC
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoOfBijectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.MonoOfInjectiveOnSimplices
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsPullbackOfUniqueSimplicesPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.SimplicesPullbackExistsUniqueOfMapEq
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisCoverOfMonoOfZariskiLocal
import Development.AutomorphicArithmetic.CommutativeAlgebra.LocallyExistsIsUnitOfSpanRangeEqTop
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductMapOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.IsIsoStackProductPairOfBijective
import Development.AutomorphicArithmetic.CommutativeAlgebra.StackProductIsPullbackOfActionPullback
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOfIsoSquare
import Development.AutomorphicArithmetic.CommutativeAlgebra.LerayHirschOneIffTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.AffineLineActionFstTwistEquiv
import Development.AutomorphicArithmetic.CommutativeAlgebra.MayerVietorisStackProductOfInjectiveOfLocallyCov
import Development.AutomorphicArithmetic.CommutativeAlgebra.PullCupPowEqCupPowPull
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjBundleFormulaIffPglForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassTateTwistCocycleUniqueNaturalAddiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistUnitClassRootClassSpecStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement
import Development.AutomorphicArithmetic.CommutativeAlgebra.FirstChernClassEqZeroOfIsTrivialized
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankOneOfHomotopyInvarian
import Development.AutomorphicArithmetic.CommutativeAlgebra.ProjectiveBundleFormulaRankTwo
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf UpperTheory.Blow

/- English proof (translation)
Simplify `h` using `[Um.join]`.
-/
private theorem isUnit_last_join {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) (h : IsUnit (x.2.1 1)) :
    IsUnit ((Um.join x).1 (Fin.last N)) := by
  simpa [Um.join] using h

/- English proof (translation)
Take `⟨u, hu⟩` from `h`. Establish `e : (Um.join x).1 '' Set.range Fin.castSucc = (fun i => (u : A) * x.1.1 i) '' Set.univ`. Use extensionality with `y`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, ⟨i, rfl⟩, rfl⟩`.

Conclude with `⟨i, trivial, by simp [Um.join, hu]⟩`. Introduce and unpack `⟨i, -, rfl⟩`. Conclude with `⟨_, ⟨i, rfl⟩, by simp [Um.join, hu]⟩`. Rewrite using `[e, span_scale, Set.image_univ]`. Conclude with `x.1.2`.
-/
private theorem closedSubgroup_cutoff_exists {N : ℕ} {A : Type} [CommRing A] (x : Um N A × Um 2 A) (h : IsUnit (x.2.1 0)) :
    Ideal.span ((Um.join x).1 '' Set.range Fin.castSucc) = ⊤ := by
  obtain ⟨u, hu⟩ := h
  have e : (Um.join x).1 '' Set.range Fin.castSucc = (fun i => (u : A) * x.1.1 i) '' Set.univ := by
    ext y
    constructor
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, trivial, by simp [Um.join, hu]⟩
    · rintro ⟨i, -, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, by simp [Um.join, hu]⟩
  rw [e, span_scale, Set.image_univ]
  exact x.1.2

/- English proof (translation)
Introduce `R _ N E`. Use `UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E _ _ (fun A => Subtype.val_injective) (fun A => Subtype.val_injective) (fun A => Function.bijective_id) (fun A => Function.bijective_id) ?_` and prove the remaining obligations. Introduce `T x`. Take `⟨S, hS, hP⟩` from `UpperTheory.locally_exists_isUnit_of_span_range_eq_top T (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1 (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.2`. Use `⟨S, hS, fun V g hg => ?_⟩` and prove the remaining obligations.

Take `⟨i, hi⟩` from `hP V g hg`. Establish `hx : (show Um N Γ(V, ⊤) × Um 2 Γ(V, ⊤) from (BC N).D.map g.appTop x).2.1 i = g.appTop.hom ((show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1 i)` using `rfl`. Rewrite `hi` using `[← hx]`. Use `fin_cases i`. Conclude with `Or.inr ⟨⟨_, closedSubgroup_cutoff_exists _ hi⟩, rfl⟩`.

Conclude with `Or.inl ⟨⟨_, isUnit_last_join _ hi⟩, rfl⟩`.
-/
theorem UpperTheory.two_open_cover_of_map_incl_comap :
    ∀ (R : Type) [CommRing R] (N : ℕ) (E : Spc),
        Cover2 R (Sp.map E (incl ((Q1 N).comap (βC N)))) (Sp.map E (incl ((Q2 N).comap (βC N)))) := by
  intro R _ N E
  refine UpperTheory.mayerVietoris_stackProduct_of_injective_of_locally_covered R E _ _ (fun A => Subtype.val_injective) (fun A => Subtype.val_injective)
    (fun A => Function.bijective_id) (fun A => Function.bijective_id) ?_
  intro T x
  obtain ⟨S, hS, hP⟩ := UpperTheory.locally_exists_isUnit_of_span_range_eq_top T (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1
    (show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.2
  refine ⟨S, hS, fun V g hg => ?_⟩
  obtain ⟨i, hi⟩ := hP V g hg
  have hx : (show Um N Γ(V, ⊤) × Um 2 Γ(V, ⊤) from (BC N).D.map g.appTop x).2.1 i =
      g.appTop.hom ((show Um N Γ(T, ⊤) × Um 2 Γ(T, ⊤) from x).2.1 i) := rfl
  rw [← hx] at hi
  fin_cases i
  · exact Or.inr ⟨⟨_, closedSubgroup_cutoff_exists _ hi⟩, rfl⟩
  · exact Or.inl ⟨⟨_, isUnit_last_join _ hi⟩, rfl⟩
