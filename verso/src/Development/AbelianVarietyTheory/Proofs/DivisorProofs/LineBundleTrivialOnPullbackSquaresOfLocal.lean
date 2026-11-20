import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenPullComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorRigidifiedLocallyTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullGeneratorFactorPairingGenericMumfordBundle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

/- English proof (translation)
Introduce `S A _ N hA hN hR T t hloc Y φ y hY`. Use `haveI := hA.comm`. Use `letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj`. Set `e : Over.mk y ≅ (Over.pullback t).obj A` to `Over.isoMk hY.isoPullback hY.isoPullback_hom_snd`. Use `letI I : GrpObj (Over.mk y) := GrpObj.ofIso e.symm`.

Establish `: IsMonHom e.symm.hom` using `CategoryTheory.isMonHom_ofIso e.symm`. Establish `: IsMonHom e.hom` using `inferInstanceAs (IsMonHom e.symm.inv)`. Establish `hP : IsGrpPullback (Over.mk y) A t φ` using `((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A t)).congr (Category.id_comp _) (by simp [e])`. Establish `hA' : IsAbelianScheme (Over.mk y)` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hP`. Use `haveI := hA'.comm`.

Take `⟨r, hr⟩` from `hR`. Establish `he : eSec (Over.mk y) ≫ φ = t ≫ eSec A` using `(cubeMapOf hP).e_comm`. Establish `g` using `rigPullOf_isGen (G' := Over.mk y) (G := A) φ t he N r hr`. Establish `hR' : Out.Rigidified (Over.mk y) (N.pull φ)` using `⟨_, g⟩`. Use `GlobalTheory.T.exists_generator_rigidified_locally_trivial T (Over.mk y) (N.pull φ) hA' (pull_isLB hN φ) hR' (fun τ => ?_)` and prove the remaining obligations.

Take `⟨V, hτ, hV⟩` from `hloc τ`. Use `⟨V, hτ, ?_⟩` and prove the remaining obligations. Establish `H : IsPullback ((y ⁻¹ᵁ V).ι ≫ φ) (y ∣_ V) A.hom (V.ι ≫ t)` using `(isPullback_morphismRestrict y V).flip.paste_horiz hY`. Conclude with `(GlobalTheory.Mum.exists_gen_pull_pull_iff hN φ (y ⁻¹ᵁ V).ι).2 (hV _ _ _ H)`.
-/
theorem trivCond_of_local : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Out.Rigidified A N → ∀ (T : Scheme.{0}) (t : T ⟶ S), (∀ τ : T, ∃ V : T.Opens, τ ∈ V ∧ TrivCond A N V (V.ι ≫ t)) → TrivCond A N T t := by
  intro S A _ N hA hN hR T t hloc Y φ y hY
  haveI := hA.comm
  letI : GrpObj ((Over.pullback t).obj A) := Functor.grpObjObj
  let e : Over.mk y ≅ (Over.pullback t).obj A := Over.isoMk hY.isoPullback hY.isoPullback_hom_snd
  letI I : GrpObj (Over.mk y) := GrpObj.ofIso e.symm
  have : IsMonHom e.symm.hom := CategoryTheory.isMonHom_ofIso e.symm
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom e.symm.inv)
  have hP : IsGrpPullback (Over.mk y) A t φ :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback A t)).congr (Category.id_comp _)
      (by simp [e])
  have hA' : IsAbelianScheme (Over.mk y) := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA hP
  haveI := hA'.comm
  obtain ⟨r, hr⟩ := hR
  have he : eSec (Over.mk y) ≫ φ = t ≫ eSec A := (cubeMapOf hP).e_comm
  have g := rigPullOf_isGen (G' := Over.mk y) (G := A) φ t he N r hr
  have hR' : Out.Rigidified (Over.mk y) (N.pull φ) := ⟨_, g⟩
  refine GlobalTheory.T.exists_generator_rigidified_locally_trivial T (Over.mk y) (N.pull φ) hA' (pull_isLB hN φ) hR' (fun τ => ?_)
  obtain ⟨V, hτ, hV⟩ := hloc τ
  refine ⟨V, hτ, ?_⟩
  have H : IsPullback ((y ⁻¹ᵁ V).ι ≫ φ) (y ∣_ V) A.hom (V.ι ≫ t) :=
    (isPullback_morphismRestrict y V).flip.paste_horiz hY
  exact (GlobalTheory.Mum.exists_gen_pull_pull_iff hN φ (y ⁻¹ᵁ V).ι).2 (hV _ _ _ H)

end GlobalTheory.TrivLocus
