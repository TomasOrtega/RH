import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOneBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsMumfordFormalSectionTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedRelationCocycleInTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdicSumTwistedSectionFamilyTendsToZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFunctionalEquationOfAdicSumTermwiseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.MumCoef

/- English proof (translation)
Simplify using `only [shift, map_add, smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem shift_add' {X : Type} [AddCommGroup X] (h h' : X →+ X) (n j : ℤ) (a b : X) :
    shift h h' n j (a + b) = shift h h' n j a + shift h h' n j b := by
  simp only [shift, map_add, smul_add]; abel

/- English proof (translation)
Simplify using `[shift]`.
-/
theorem shift_zero' {X : Type} [AddCommGroup X] (h h' : X →+ X) (n j : ℤ) :
    shift h h' n j 0 = 0 := by
  simp [shift]

/- English proof (translation)
Introduce `R _ _ _ hB D a a' h h' hE N hN hP σ₀`. Take `⟨s₀, s, hrel, hsmall, hvan, hσ⟩` from `GlobalTheory.T.exists_terms_mumfordFormalSection_translates R hB D a a' h h' hE N hN hP σ₀`. Take `⟨F, hsum, hFs⟩` from `GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hB D a (N : ℤ) (-1) D.toPre.X (shift h h' (N : ℤ) (-1)) s hsmall`. Establish `hw0 : shift h h' (N : ℤ) (-1) (0 : D.toPre.X) = 0` using `shift_zero' h h' _ _`. Establish `hfe : TFE h h' F`.

Use `GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise R hB D a a' h h' hE (N : ℤ) (-1) D.toPre.X (shift h h' (N : ℤ) (-1)) s F (fun mu => Equiv.addRight mu) hsmall hsum ?_ ?_` and prove the remaining obligations. Introduce `mu i`. Conclude with `shift_add' h h' _ _ i mu`. Introduce `mu i`. Conclude with `GlobalTheory.T.twistedRelation_cocycle_in_translation R hB D a a' h h' hE (N : ℤ) (-1) i mu 0 _ _ s₀ (s i) (s (i + mu)) (zero_add _).symm (shift_add' h h' _ _ i mu) (hrel i) (hrel (i + mu))`.

Establish `hv0 : ∀ i ∉ ({0} : Finset D.toPre.X), Van (maximalIdeal R) (s i) 0` using `fun i hi => hvan i (by simpa using hi)`. Use `⟨F, hFs, hfe, ?_, ?_⟩` and prove the remaining obligations. Introduce `β hβ Z x z J hJ`. Rewrite using `[hsum 0 {0} hv0 β Z x z J hJ]`. Establish `: ({0} : Finset D.toPre.X).filter (fun i => shift h h' (N : ℤ) (-1) i = β) = ∅`.

Rewrite using `[Finset.filter_singleton, hw0, if_neg (Ne.symm hβ)]`. Rewrite using `[this, Finset.sum_empty]`. Introduce `Z x z J hJ`. Rewrite using `[hsum 0 {0} hv0 0 Z x z J hJ]`. Establish `: ({0} : Finset D.toPre.X).filter (fun i => shift h h' (N : ℤ) (-1) i = 0) = {0}`.

Rewrite using `[Finset.filter_singleton, hw0, if_pos rfl]`. Rewrite using `[this, Finset.sum_singleton]`. Conclude with `hσ Z _ z J hJ`.
-/
theorem coef : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → GlobalTheory.MumMult.PosN D a h h' N → ∀ (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1])), ∃ g : ∀ β, SecT D.toPre a N (-1) β, Small (maximalIdeal R) (w := id) g ∧ TFE h h' g ∧ (∀ β, β ≠ 0 → Van (maximalIdeal R) (g β) 0) ∧ ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).left) (z : Z) (J), Good D.toPre.P.L z J → sval (g 0) (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J = sval σ₀ (x ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) z J := by
  classical
  intro R _ _ _ hB D a a' h h' hE N hN hP σ₀
  obtain ⟨s₀, s, hrel, hsmall, hvan, hσ⟩ := GlobalTheory.T.exists_terms_mumfordFormalSection_translates R hB D a a' h h' hE N hN hP σ₀
  obtain ⟨F, hsum, hFs⟩ := GlobalTheory.T.exists_adicSum_twistedSectionFamily_tendsToZero R hB D a (N : ℤ) (-1) D.toPre.X (shift h h' (N : ℤ) (-1)) s hsmall
  have hw0 : shift h h' (N : ℤ) (-1) (0 : D.toPre.X) = 0 := shift_zero' h h' _ _
  have hfe : TFE h h' F := by
    refine GlobalTheory.T.twistedFunctionalEquation_of_adicSum_termwise R hB D a a' h h' hE (N : ℤ) (-1) D.toPre.X (shift h h' (N : ℤ) (-1)) s F
      (fun mu => Equiv.addRight mu) hsmall hsum ?_ ?_
    · intro mu i
      exact shift_add' h h' _ _ i mu
    · intro mu i
      exact GlobalTheory.T.twistedRelation_cocycle_in_translation R hB D a a' h h' hE (N : ℤ) (-1) i mu 0 _ _ s₀ (s i) (s (i + mu))
        (zero_add _).symm (shift_add' h h' _ _ i mu) (hrel i) (hrel (i + mu))
  have hv0 : ∀ i ∉ ({0} : Finset D.toPre.X), Van (maximalIdeal R) (s i) 0 := fun i hi =>
    hvan i (by simpa using hi)
  refine ⟨F, hFs, hfe, ?_, ?_⟩
  · intro β hβ Z x z J hJ
    rw [hsum 0 {0} hv0 β Z x z J hJ]
    have : ({0} : Finset D.toPre.X).filter (fun i => shift h h' (N : ℤ) (-1) i = β) = ∅ := by
      rw [Finset.filter_singleton, hw0, if_neg (Ne.symm hβ)]
    rw [this, Finset.sum_empty]
  · intro Z x z J hJ
    rw [hsum 0 {0} hv0 0 Z x z J hJ]
    have : ({0} : Finset D.toPre.X).filter (fun i => shift h h' (N : ℤ) (-1) i = 0) = {0} := by
      rw [Finset.filter_singleton, hw0, if_pos rfl]
    rw [this, Finset.sum_singleton]
    exact hσ Z _ z J hJ

end GlobalTheory.MumCoef
