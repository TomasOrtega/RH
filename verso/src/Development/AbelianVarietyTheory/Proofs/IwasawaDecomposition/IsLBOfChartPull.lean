import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNonzeroLocusFormMap
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsIsoOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProper
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.NefFibre

/- English proof (translation)
Use `GlobalTheory.GenSpread.isLB_of_gm A hc fun y i j k hi hj hk => ?_` and prove the remaining obligations. Establish `hi' : y ∈ M.U (a.idx i)` using `a.le i hi`. Establish `hj' : y ∈ M.U (a.idx j)` using `a.le j hj`. Establish `hk' : y ∈ M.U (a.idx k)` using `a.le k hk`. Rewrite using `[a.g y i j hi hj, a.g y j k hj hk, a.g y i k hi hk]`.

Conclude with `gm_cocycle hM (𝟙 Y) y hi' hj' hk'`.
-/
theorem isLB_of_chartPull {Y : Scheme.{0}} {A M : LB Y} (a : ChartPull A M (𝟙 Y)) (hM : M.IsLB)
    (hc : ∀ y : Y, ∃ i, y ∈ A.U i) : A.IsLB := by
  refine GlobalTheory.GenSpread.isLB_of_gm A hc fun y i j k hi hj hk => ?_
  have hi' : y ∈ M.U (a.idx i) := a.le i hi
  have hj' : y ∈ M.U (a.idx j) := a.le j hj
  have hk' : y ∈ M.U (a.idx k) := a.le k hk
  rw [a.g y i j hi hj, a.g y j k hj hk, a.g y i k hi hk]
  exact gm_cocycle hM (𝟙 Y) y hi' hj' hk'

/- English proof (translation)
Introduce `R _ Z X s b hs hbs L P _ h`. Use `set κ := P.ResidueField`. Use `set t := spMap (algebraMap R κ)`. Set `` to `GlobalTheory.algebraΓOfHom (pullback.snd s t)`. Set `` to `GlobalTheory.algebraΓOfHom (pullback.snd (b ≫ s) t)`.

Set `bP : pullback (b ≫ s) t ⟶ pullback s t` to `pullback.map (b ≫ s) t s t b (𝟙 _) (𝟙 _) (by simp) (by simp)`. Establish `hfst : bP ≫ pullback.fst s t = pullback.fst (b ≫ s) t ≫ b` using `pullback.lift_fst _ _ _`. Establish `hsnd : bP ≫ pullback.snd s t = pullback.snd (b ≫ s) t` using `(pullback.lift_snd _ _ _).trans (Category.comp_id _)`. Take `⟨hpZ, A, hA⟩` from `(GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap R κ) hs)`. Take `⟨hpX, A', hA'⟩` from `(GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1 (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap R κ) hbs)`.

Establish `: IsProper (GlobalTheory.strHom κ (pullback s t))`. Rewrite using `[GlobalTheory.strHom_eq (f := pullback.snd s t) fun _ => rfl]` and apply the resulting hypothesis. Establish `: IsProper (bP ≫ pullback.snd s t)` using `by rw [hsnd]; exact hpX`. Establish `: IsProper bP` using `IsProper.of_comp bP (pullback.snd s t)`. Establish `hN` using `GlobalTheory.PosBaseChange.isNef_pull (E := κ) h hA hA' bP bP.isClosedMap`.

Establish `hM : ((L.pull (pullback.fst s t)).pull bP).IsLB` using `hN.isLB`. Establish `a : ChartPull ((L.pull b).pull (pullback.fst (b ≫ s) t)) ((L.pull (pullback.fst s t)).pull bP) (𝟙 _)` using `GlobalTheory.chartPullPullLinComb L (fun _ : PUnit => b) (fun _ => 1) (pullback.fst (b ≫ s) t) (pullback.fst s t) (fun _ => bP) fun _ => hfst`. Establish `hL : ((L.pull b).pull (pullback.fst (b ≫ s) t)).IsLB`. Use `isLB_of_chartPull a hM fun y => ?_` and prove the remaining obligations. Take `⟨J, hJ⟩` from `exists_chart hM y`.

Use `⟨fun _ _ => J PUnit.unit PUnit.unit, ?_⟩` and prove the remaining obligations. Establish `h1 : (pullback.fst s t) (bP y) ∈ L.U (J PUnit.unit PUnit.unit)` using `mem_pull.1 (mem_pull.1 hJ)`. Rewrite `h1` using `[← Scheme.Hom.comp_apply, hfst, Scheme.Hom.comp_apply]`. Conclude with `mem_pull.2 (mem_pull.2 h1)`. Conclude with `GlobalTheory.IsNef.of_lbIso hN hL (LBIso.chartPull a (chartPullId _) ⟨_, idIso_isGen hM⟩)`.
-/
theorem isNef_fibre_pull : ∀ (R : Type) [CommRing R] (Z X : Scheme.{0}) (s : Z ⟶ Sp R) (b : X ⟶ Z), IsProjOver s →
    IsProjOver (b ≫ s) → ∀ (L : LB Z) (P : Ideal R) [P.IsPrime],
    (letI := GlobalTheory.algebraΓOfHom (pullback.snd s (spMap (algebraMap R P.ResidueField)));
      GlobalTheory.IsNef P.ResidueField (L.pull (pullback.fst s (spMap (algebraMap R P.ResidueField))))) →
    (letI := GlobalTheory.algebraΓOfHom (pullback.snd (b ≫ s) (spMap (algebraMap R P.ResidueField)));
      GlobalTheory.IsNef P.ResidueField ((L.pull b).pull (pullback.fst (b ≫ s) (spMap (algebraMap R P.ResidueField))))) := by
  intro R _ Z X s b hs hbs L P _ h
  set κ := P.ResidueField
  set t := spMap (algebraMap R κ)
  let := GlobalTheory.algebraΓOfHom (pullback.snd s t)
  let := GlobalTheory.algebraΓOfHom (pullback.snd (b ≫ s) t)
  let bP : pullback (b ≫ s) t ⟶ pullback s t :=
    pullback.map (b ≫ s) t s t b (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hfst : bP ≫ pullback.fst s t = pullback.fst (b ≫ s) t ≫ b := pullback.lift_fst _ _ _
  have hsnd : bP ≫ pullback.snd s t = pullback.snd (b ≫ s) t :=
    (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  obtain ⟨hpZ, A, hA⟩ := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1
    (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap R κ) hs)
  obtain ⟨hpX, A', hA'⟩ := (GlobalTheory.isProjOver_iff_isProper_and_exists_isAmpleLB _).1
    (GlobalTheory.ProjSpace.isProjOver_pullback_snd (algebraMap R κ) hbs)
  have : IsProper (GlobalTheory.strHom κ (pullback s t)) := by
    rwa [GlobalTheory.strHom_eq (f := pullback.snd s t) fun _ => rfl]
  have : IsProper (bP ≫ pullback.snd s t) := by rw [hsnd]; exact hpX
  have : IsProper bP := IsProper.of_comp bP (pullback.snd s t)
  have hN := GlobalTheory.PosBaseChange.isNef_pull (E := κ) h hA hA' bP bP.isClosedMap
  have hM : ((L.pull (pullback.fst s t)).pull bP).IsLB := hN.isLB
  have a : ChartPull ((L.pull b).pull (pullback.fst (b ≫ s) t)) ((L.pull (pullback.fst s t)).pull bP)
      (𝟙 _) :=
    GlobalTheory.chartPullPullLinComb L (fun _ : PUnit => b) (fun _ => 1) (pullback.fst (b ≫ s) t) (pullback.fst s t)
      (fun _ => bP) fun _ => hfst
  have hL : ((L.pull b).pull (pullback.fst (b ≫ s) t)).IsLB := by
    refine isLB_of_chartPull a hM fun y => ?_
    obtain ⟨J, hJ⟩ := exists_chart hM y
    refine ⟨fun _ _ => J PUnit.unit PUnit.unit, ?_⟩
    have h1 : (pullback.fst s t) (bP y) ∈ L.U (J PUnit.unit PUnit.unit) := mem_pull.1 (mem_pull.1 hJ)
    rw [← Scheme.Hom.comp_apply, hfst, Scheme.Hom.comp_apply] at h1
    exact mem_pull.2 (mem_pull.2 h1)
  exact GlobalTheory.IsNef.of_lbIso hN hL (LBIso.chartPull a (chartPullId _) ⟨_, idIso_isGen hM⟩)

end GlobalTheory.NefFibre
