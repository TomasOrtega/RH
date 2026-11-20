import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.TransCancel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PowerOfAbelianSchemeProjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

/- English proof (translation)
Establish `hiso : ∀ {X Y : Over S} (e : X ≅ Y), Smooth Y.hom → Smooth X.hom`. Introduce `X Y e h`. Rewrite using `[← Over.w e.hom]`. Establish `: IsIso e.hom.left` using `inferInstanceAs (IsIso ((Over.forget S).mapIso e).hom)`. Use `infer_instance`.

Establish `hprod : ∀ (Y Z : Over S), Smooth Y.hom → Smooth Z.hom → Smooth (Y ⨯ Z).hom`. Introduce `Y Z hY hZ`. Rewrite using `[← Over.w (prod.snd (X := Y) (Y := Z)), ← Over.prodLeftIsoPullback_hom_snd]`. Use `infer_instance`. Proceed by induction on `k with`.

Consider the case `zero`. Conclude with `hiso (((isLimitEquivIsTerminalOfIsEmpty _ _) (productIsProduct _)).uniqueUpToIso Over.mkIdTerminal) (by dsimp; infer_instance)`. Consider the case `succ k ih`. Conclude with `hiso ((productIsProduct _).conePointUniqueUpToIso (extendFanIsLimit _ (productIsProduct fun _ : Fin k => A) (prodIsProd _ _))) (hprod _ _ hA ih)`.
-/
private lemma smooth_pow_hom {S : Scheme.{0}} (A : Over S) (hA : Smooth A.hom) (k : ℕ) :
    Smooth (GlobalTheory.KS.pow A k).hom := by
  have hiso : ∀ {X Y : Over S} (e : X ≅ Y), Smooth Y.hom → Smooth X.hom := by
    intro X Y e h
    rw [← Over.w e.hom]
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).hom)
    infer_instance
  have hprod : ∀ (Y Z : Over S), Smooth Y.hom → Smooth Z.hom → Smooth (Y ⨯ Z).hom := by
    intro Y Z hY hZ
    rw [← Over.w (prod.snd (X := Y) (Y := Z)), ← Over.prodLeftIsoPullback_hom_snd]
    infer_instance
  induction k with
  | zero =>
    exact hiso (((isLimitEquivIsTerminalOfIsEmpty _ _) (productIsProduct _)).uniqueUpToIso
      Over.mkIdTerminal) (by dsimp; infer_instance)
  | succ k ih =>
    exact hiso ((productIsProduct _).conePointUniqueUpToIso
      (extendFanIsLimit _ (productIsProduct fun _ : Fin k => A) (prodIsProd _ _))) (hprod _ _ hA ih)

/- English proof (translation)
Introduce `hG p _ D R _ _ gb N X k`. Take `⟨hs, hsep, -, hproj⟩` from `hG p D R gb N X`. Use `haveI := hs`. Use `haveI := hsep`. Use `haveI : Smooth X.univ.A.hom := X.univ.ab.smooth`.

Use `haveI : Smooth (GlobalTheory.KS.pow X.univ.A k).hom := smooth_pow_hom _ inferInstance k`. Use `haveI : IsProper (GlobalTheory.KS.pow X.univ.A k).hom := GlobalTheory.KS.Leray.isProper_pow_hom _ X.univ.ab.proper k`. Use `⟨inferInstance, inferInstance, fun hD => ?_⟩` and prove the remaining obligations. Conclude with `GlobalTheory.KS.isProjOver_pow R X.X X.s (hproj hD) X.univ.A X.univ.ab _ (LB.isLB_pull X.univ.isLB _) X.univ.ample k`.
-/
theorem UpperTheory.Gal.G3.pPowSm :
    GenSm → PowSm := by
  intro hG p _ D R _ _ gb N X k
  obtain ⟨hs, hsep, -, hproj⟩ := hG p D R gb N X
  haveI := hs
  haveI := hsep
  haveI : Smooth X.univ.A.hom := X.univ.ab.smooth
  haveI : Smooth (GlobalTheory.KS.pow X.univ.A k).hom := smooth_pow_hom _ inferInstance k
  haveI : IsProper (GlobalTheory.KS.pow X.univ.A k).hom :=
    GlobalTheory.KS.Leray.isProper_pow_hom _ X.univ.ab.proper k
  refine ⟨inferInstance, inferInstance, fun hD => ?_⟩
  exact GlobalTheory.KS.isProjOver_pow R X.X X.s (hproj hD) X.univ.A X.univ.ab _
    (LB.isLB_pull X.univ.isLB _) X.univ.ample k
