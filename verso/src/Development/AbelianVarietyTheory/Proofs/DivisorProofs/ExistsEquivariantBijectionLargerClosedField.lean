import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LabExt
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.SeriesFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExtensionSecPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueFieldExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsAlgClosureFractionRingBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearEquivExtensionFieldBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionPointFromFractionAlgClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralThetaFamilyOverDegenerationFamilyPullbacStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivariantLinearExtensionToAlgClosedFieldStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.UpExt
open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

/- English proof (translation)
Introduce `R _ _ _ hR D A N hN lab E₀ Φ hE hΦ F _ _ _ em lab' hlab`. Establish `hN1 : 1 ≤ N` using `hN.pos`. Use `haveI : CharZero R := hR.2`. Use `letI : Algebra (Kb R) F := em.toAlgebra`. Use `haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm`.

Establish `hem : IsScalarTower.toAlgHom (FractionRing R) (Kb R) F = em` using `AlgHom.ext fun _ => rfl`. Set `e : Fam D.toPre (Kb R) N →ₗ[Kb R] SecF A (Kb R) N` to `{ toFun := E₀ map_add' := fun s t => SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j map_smul' := fun c s => SecOver.ext _ _ fun j => hE.smul c s (c • s) ((isSmul_iff _ _ _).2 rfl) j }`. Take `⟨e', he', hc⟩` from `GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange _ _ _ _ _ _ (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N) (secPull A (Kb R) F N) (isExtension_famPull _ _ _ GlobalTheory.globalFns_holds hN1) (isExtension_secPull A (Kb R) F N) e hE.bij`. Establish `hq` using `GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre F em N hN1`. Establish `onto : ∀ x : TFK (R` using `R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x := by`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨y, hy, hxy⟩` from `GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure R A F em N hN1 x hx`. Take `⟨p₀, hp₀⟩` from `(hE.onto y).1 hy`.

Take `⟨p', hp', -⟩` from `hq.1 p₀`. Use `⟨p', Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Rewrite using `[hlab p₀ p' hp', hp₀, hxy]`. Introduce and unpack `⟨p, rfl⟩`. Take `⟨p₀, hp₀, -⟩` from `hq.2 p`.

Establish `hy` using `(hE.onto (lab p₀)).2 ⟨p₀, rfl⟩`. Establish `e1 : lab' p = baseK (Kb R) F ≫ lab p₀` using `Over.OverMorphism.ext (hlab p₀ p hp₀)`. Rewrite using `[e1, ← MonObj.comp_pow, hy, MonObj.comp_one]`. Use `⟨fun s => e' s, ⟨he', fun s s' s'' h j => ?_, fun c s s' h j => ?_, onto, fun p => ((GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hR.1 D F N hN p).1), fun p => GlobalTheory.SymFrameClause.exists_symLift R A F N hN (lab' p) ((onto _).2 ⟨p, rfl⟩), fun …` and prove the remaining obligations. Take `rfl : s'' = s + s'` from `fam_ext h`.

Rewrite using `[map_add]`. Both sides reduce to the same expression. Take `rfl : s' = c • s` from `(isSmul_iff _ _ _).1 h`. Rewrite using `[map_smul]`. Both sides reduce to the same expression.

Introduce `F₀ s hs`. Take `⟨s₀, hs₀, -⟩` from `GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)`. Establish `h1` using `GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback R (maximalIdeal R) D.toPre N F₀ (Kb R) F s₀ hs₀`. Take `rfl` from `(GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ F).unique hs h1`. Introduce `Z p p' hpp z J hJ`.

Use `show sval (e' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s₀)) p z J = _`. Rewrite using `[hc]`. Use `(sval_pullOver _ _ _ _ hJ).trans (hΦ F₀ s₀ hs₀ Z (p ≫ (secMap A (Kb R) F).left) p' ?_ z J hJ)` and prove the remaining obligations. Rewrite using `[Category.assoc, ← hpp]`. Conclude with `congrArg (p ≫ ·) (congrArg (fun q => q.left) (secMap_snd A (Kb R) F))`.
-/
theorem exists_eqv_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E₀ (Φ : IntFam (maximalIdeal R) D.toPre N → H0 A.L N), Eqv D.toPre A (Kb R) N lab E₀ → (∀ F₀ s, F₀.Over s → Agree A.L (E₀ s) (Φ F₀)) → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (em : Kb R →ₐ[FractionRing R] F) lab', LabExt em lab lab' → ∃ E', Eqv D.toPre A F N lab' E' ∧ ∀ F₀ s, F₀.Over s → Agree A.L (E' s) (Φ F₀) := by
  intro R _ _ _ hR D A N hN lab E₀ Φ hE hΦ F _ _ _ em lab' hlab
  have hN1 : 1 ≤ N := hN.pos
  haveI : CharZero R := hR.2
  letI : Algebra (Kb R) F := em.toAlgebra
  haveI : IsScalarTower (FractionRing R) (Kb R) F := IsScalarTower.of_algebraMap_eq fun x => (em.commutes x).symm
  have hem : IsScalarTower.toAlgHom (FractionRing R) (Kb R) F = em := AlgHom.ext fun _ => rfl
  let e : Fam D.toPre (Kb R) N →ₗ[Kb R] SecF A (Kb R) N :=
    { toFun := E₀
      map_add' := fun s t => SecOver.ext _ _ fun j => hE.add s t (s + t) (fun _ _ => rfl) j
      map_smul' := fun c s => SecOver.ext _ _ fun j => hE.smul c s (c • s) ((isSmul_iff _ _ _).2 rfl) j }
  obtain ⟨e', he', hc⟩ := GlobalTheory.T.exists_linearEquiv_extension_fieldBaseChange _ _ _ _ _ _ (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N) (secPull A (Kb R) F N)
    (isExtension_famPull _ _ _ GlobalTheory.globalFns_holds hN1) (isExtension_secPull A (Kb R) F N) e hE.bij
  have hq := GlobalTheory.T.levelPoints_algClosure_fractionRing_bijective R D.toPre F em N hN1
  have onto : ∀ x : TFK (R := R) F ⟶ A.A, x ^ N = 1 ↔ ∃ p, lab' p = x := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hxy⟩ := GlobalTheory.T.exists_torsion_point_from_fractionAlgClosure R A F em N hN1 x hx
      obtain ⟨p₀, hp₀⟩ := (hE.onto y).1 hy
      obtain ⟨p', hp', -⟩ := hq.1 p₀
      refine ⟨p', Over.OverMorphism.ext ?_⟩
      rw [hlab p₀ p' hp', hp₀, hxy]
    · rintro ⟨p, rfl⟩
      obtain ⟨p₀, hp₀, -⟩ := hq.2 p
      have hy := (hE.onto (lab p₀)).2 ⟨p₀, rfl⟩
      have e1 : lab' p = baseK (Kb R) F ≫ lab p₀ := Over.OverMorphism.ext (hlab p₀ p hp₀)
      rw [e1, ← MonObj.comp_pow, hy, MonObj.comp_one]
  refine ⟨fun s => e' s, ⟨he', fun s s' s'' h j => ?_, fun c s s' h j => ?_, onto,
    fun p => ((GlobalTheory.UT.SymFrame.main GlobalTheory.firstFiveLaws R (maximalIdeal R) hR.1 D F N hN p).1),
    fun p => GlobalTheory.SymFrameClause.exists_symLift R A F N hN (lab' p) ((onto _).2 ⟨p, rfl⟩),
    fun p w θ s s' hw hθ hs => GlobalTheory.T.equivariant_linearExtension_to_algClosedField R hR D A N hN lab E₀ hE F lab' (hem ▸ hlab) e' hc p w θ s s' hw hθ hs⟩, ?_⟩
  · obtain rfl : s'' = s + s' := fam_ext h
    rw [map_add]
    rfl
  · obtain rfl : s' = c • s := (isSmul_iff _ _ _).1 h
    rw [map_smul]
    rfl
  · intro F₀ s hs
    obtain ⟨s₀, hs₀, -⟩ := GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ (Kb R)
    have h1 := GlobalTheory.T.integralThetaFamily_over_degenerationFamilyPullback R (maximalIdeal R) D.toPre N F₀ (Kb R) F s₀ hs₀
    obtain rfl := (GlobalTheory.T.existsUnique_fieldExtension R (maximalIdeal R) D.toPre N F₀ F).unique hs h1
    intro Z p p' hpp z J hJ
    show sval (e' (famPull D.toPre (Kb R) F GlobalTheory.globalFns_holds N s₀)) p z J = _
    rw [hc]
    refine (sval_pullOver _ _ _ _ hJ).trans (hΦ F₀ s₀ hs₀ Z (p ≫ (secMap A (Kb R) F).left) p' ?_ z J hJ)
    rw [Category.assoc, ← hpp]
    exact congrArg (p ≫ ·) (congrArg (fun q => q.left) (secMap_snd A (Kb R) F))
end GlobalTheory.Mum.UpExt
