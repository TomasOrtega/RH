import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianOfGenericAbelianOfClosedIsGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TqOfGtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvenOnTorusDescendsAlongLocalHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ _ D G _ _ P hG hU X _ _ _ hQ`. Take `⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, -, hφ, hgp, hL, -⟩` from `hU`. Establish `hadm : AdmBase W (maximalIdeal W)` using `by haveI := hW.1`. Conclude with `⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩`. Establish `hG' : IsSemiAbelian G'`.

Take `⟨bc, mbc, -⟩` from `grpPullback_iso hgp (isGrpPullback_pullback G (spMap φ))`. Use `haveI := mbc`. Conclude with `GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G hG)`. Take `⟨P', hP', hE⟩` from `unif_evenOn W hadm D' A' G' hG' U'`. Establish `hpr : IsProper (pullback.snd G'.hom (jK W))`.

Use `A'.isAb.proper` as an intermediate fact. Use `haveI : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))`. Express the relevant statement in the definitionally equal form `IsProper ((Over.pullback (jK W)).obj G').hom`. Rewrite using `[← Over.w U'.gen.hom]`. Use `infer_instance`.

Establish `hL' : LBIso P'.L.L (P.L.L.pull β)` using `by rw [hP']; exact hL`. Conclude with `GlobalTheory.T.evenOnTorus_descends_along_localHom R W φ hφ G hG G' β hgp hpr P P' hL' hE X hQ`.
-/
theorem evenOn_of_unifTrait : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R))
    (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (P : GlobalTheory.UU.CP G), IsSemiAbelian G → UnifTrait D G P.L.L →
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X],
    Nonempty (GlobalTheory.UU.TQ (thickObj R (maximalIdeal R) 0 G) X) → EvenOn P := by
  intro R _ _ _ _ D G _ _ P hG hU X _ _ _ hQ
  obtain ⟨W, _, _, _, φ, G', _, _, β, D', A', U', hW, -, hφ, hgp, hL, -⟩ := hU
  have hadm : AdmBase W (maximalIdeal W) := by
    haveI := hW.1
    exact ⟨inferInstance, inferInstance, inferInstance, hW.2.1⟩
  have hG' : IsSemiAbelian G' := by
    obtain ⟨bc, mbc, -⟩ := grpPullback_iso hgp (isGrpPullback_pullback G (spMap φ))
    haveI := mbc
    exact GlobalTheory.isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback (spMap φ) G hG)
  obtain ⟨P', hP', hE⟩ := unif_evenOn W hadm D' A' G' hG' U'
  have hpr : IsProper (pullback.snd G'.hom (jK W)) := by
    have := A'.isAb.proper
    haveI : IsIso U'.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U'.gen.hom))
    change IsProper ((Over.pullback (jK W)).obj G').hom
    rw [← Over.w U'.gen.hom]
    infer_instance
  have hL' : LBIso P'.L.L (P.L.L.pull β) := by rw [hP']; exact hL
  exact GlobalTheory.T.evenOnTorus_descends_along_localHom R W φ hφ G hG G' β hgp hpr P P' hL' hE X hQ

end GlobalTheory.Mum
