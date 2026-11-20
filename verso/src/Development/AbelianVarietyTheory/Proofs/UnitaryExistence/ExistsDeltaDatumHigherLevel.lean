import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.NormsFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegPFree
import Formalism.LocalToGlobal.ProjectiveLattices.RegQFree
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
import Formalism.LocalToGlobal.ProjectiveLattices.IsGenFrGenFr
import Formalism.LocalToGlobal.ProjectiveLattices.ChartDirectionsIntegral
import Formalism.LocalToGlobal.ProjectiveLattices.AllTest
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliSchemeLevelMapsHeckePointsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FramedPointsLiftToLevelCoverStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsNab
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.LevelCover

/- English proof (translation)
Establish `: CompactSpace ↥(pullback f x)` using `QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)`. Take `⟨p, -⟩` from `(pullback.snd f x).surjective (default : PrimeSpectrum F)`. Take `⟨q, -, hq⟩` from `isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩`. Use `⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]`.
-/
theorem exists_lift_of_finite_surjective {F : Type} [Field F] [IsAlgClosed F] {X Y : Scheme.{0}} (f : X ⟶ Y)
    [IsFinite f] [Surjective f] (x : Sp F ⟶ Y) : ∃ b : Sp F ⟶ X, b ≫ f = x := by
  have : CompactSpace ↥(pullback f x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd f x)
  obtain ⟨p, -⟩ := (pullback.snd f x).surjective (default : PrimeSpectrum F)
  obtain ⟨q, -, hq⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback f x)) ⟨p, trivial⟩
  refine ⟨pointOfClosedPoint (pullback.snd f x) q hq ≫ pullback.fst f x, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

/- English proof (translation)
Use `⟨fun p q φ y z _ => by simp, fun p t y y' _ => ?_⟩` and prove the remaining obligations. Establish `: wchar (ex Dw 0 0) t = 1`. Unfold `wchar`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Apply the tactic sequence `cases i <;> simp [ex]`.

Simplify using `[this]`.
-/
theorem one_mem_sec_zero {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    (1 : Rul Xo c) ∈ sec Xo c 0 0 := by
  refine ⟨fun p q φ y z _ => by simp, fun p t y y' _ => ?_⟩
  have : wchar (ex Dw 0 0) t = 1 := by
    unfold wchar
    refine Finset.prod_eq_one fun i _ => ?_
    cases i <;> simp [ex]
  simp [this]

/- English proof (translation)
Establish `hw : x ≫ Xo.s = spMap (algebraMap c.F k) ≫ spMap (IntermediateField.inclusion c.le).toRingHom`. Rewrite using `[hx, sOf, ← Spec.map_comp]`. Both sides reduce to the same expression. Take `⟨b, hb⟩` from `exists_lift_of_finite_surjective rF (pullback.lift x (spMap (algebraMap c.F k)) hw)`. Use `⟨b ≫ pullback.fst _ _, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Category.assoc, ← h₁, ← Category.assoc, hb, pullback.lift_fst]`. Establish `e : b ≫ pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom = spMap (algebraMap c.F k)`. Rewrite using `[← h₂, ← Category.assoc, hb, pullback.lift_snd]`. Take `⟨g, hg⟩` from `Spec.map_surjective (b ≫ pullback.snd _ _ : Sp k ⟶ Sp c₂.F)`. Rewrite `e` using `[← Category.assoc, ← hg, ← Spec.map_comp]`.

Establish `e'` using `Spec.map_injective e`. Establish `hgk : g = CommRingCat.ofHom (algebraMap c₂.F k)`. Use extensionality with `a`. Establish `ha : IntermediateField.inclusion hc.le ⟨a.1, hc.ge a.2⟩ = a` using `rfl`. Use `congrArg (fun f : CommRingCat.of c.F ⟶ CommRingCat.of k => f.hom ⟨a.1, hc.ge a.2⟩) e'` as an intermediate fact.

Simplify using `only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this`. Rewrite `this` using `[← hk]`. Conclude with `this`. Rewrite using `[Category.assoc, pullback.condition, ← Category.assoc, ← hg, hgk, sOf, ← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem exists_point_over {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l l₂ : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    {Xo₂ : Moduli Dw l₂} {c₂ : Coeff l₂} (hc : c.F = c₂.F) (r : Xo₂.X ⟶ Xo.X) (rF : Xo₂.XF c₂ ⟶ Xo.XF c)
    [IsFinite rF] [Surjective rF]
    (h₁ : rF ≫ pullback.fst _ _ = pullback.fst _ _ ≫ r)
    (h₂ : rF ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom)
    (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra c₂.F k]
    (hk : ∀ a : c.F, algebraMap c₂.F k (IntermediateField.inclusion hc.le a) = algebraMap c.F k a)
    (x : Sp k ⟶ Xo.X) (hx : x ≫ Xo.s = sOf c k) :
    ∃ x₂ : Sp k ⟶ Xo₂.X, x₂ ≫ r = x ∧ x₂ ≫ Xo₂.s = sOf c₂ k := by
  have hw : x ≫ Xo.s = spMap (algebraMap c.F k) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hx, sOf, ← Spec.map_comp]; rfl
  obtain ⟨b, hb⟩ := exists_lift_of_finite_surjective rF (pullback.lift x (spMap (algebraMap c.F k)) hw)
  refine ⟨b ≫ pullback.fst _ _, ?_, ?_⟩
  · rw [Category.assoc, ← h₁, ← Category.assoc, hb, pullback.lift_fst]
  · have e : b ≫ pullback.snd _ _ ≫ spMap (IntermediateField.inclusion hc.le).toRingHom =
        spMap (algebraMap c.F k) := by
      rw [← h₂, ← Category.assoc, hb, pullback.lift_snd]
    obtain ⟨g, hg⟩ := Spec.map_surjective (b ≫ pullback.snd _ _ : Sp k ⟶ Sp c₂.F)
    rw [← Category.assoc, ← hg, ← Spec.map_comp] at e
    have e' := Spec.map_injective e
    have hgk : g = CommRingCat.ofHom (algebraMap c₂.F k) := by
      ext a
      have ha : IntermediateField.inclusion hc.le ⟨a.1, hc.ge a.2⟩ = a := rfl
      have := congrArg (fun f : CommRingCat.of c.F ⟶ CommRingCat.of k => f.hom ⟨a.1, hc.ge a.2⟩) e'
      simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
      rw [← hk] at this
      exact this
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← hg, hgk, sOf, ← Spec.map_comp]
    rfl

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c hr n pd I l₂ Xo₂ c₂ hF hd hM hcop hMb hI`. Establish `hL` using `GlobalTheory.firstFiveLaws.1`. Take `⟨r, jK, m, -, -, he, heA, -, hrF⟩` from `(GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hr).1 l l₂ Xo Xo₂ hd`. Take `⟨rF, h₁, h₂, hfin, -, hsur, -⟩` from `hrF c c₂ hF.symm`. Take `⟨st, nab, hnab⟩` from `GlobalTheory.CanonConn.exists_isNab hL E H Dw l₂ Xo₂ c₂`.

Set `d : DeltaDat Xo c n` to `{ pd := pd, I := I, l₂ := l₂, Xo₂ := Xo₂, c₂ := c₂, hF := hF, r := r, m := m, nab₂ := nab, cδ := 1, φδ := fun _ => 1 }`. Establish `hdiv : l₂.M / l.M = pd`. Rewrite using `[hM]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)`. Use `⟨d, rfl, rfl, rfl, HEq.rfl, HEq.rfl, rfl, ⟨hd, hM, hcop, hMb, hI, ⟨?_, heA⟩, ?_, one_mem_sec_zero Xo₂ c₂, ?_⟩, st, hnab⟩` and prove the remaining obligations. Rewrite `he` using `[hdiv]`.

Conclude with `he`. Introduce `k _ _ _ i₂ hk y`. Take `⟨x₂, hx, hs⟩` from `@exists_point_over E _ _ _ H Dw l l₂ Xo c Xo₂ c₂ hF.symm r rF hfin hsur h₁ h₂ k _ _ _ i₂ hk y.x y.x_over`. Take `⟨y₂, -, hy⟩` from `(GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n d).1 k hk y x₂ hx hs`. Conclude with `⟨y₂, hy⟩`.

Introduce `k _ _ _ y₂`. Establish `h` using `GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l₂ Xo₂ c₂ k y₂`. Establish `e : evR d.Xo₂ d.c₂ d.cδ y₂ = 1` using `evalAt_one _ _ y₂ h`. Rewrite using `[e]`. Conclude with `one_ne_zero`.
-/
theorem exists_deltaDat_isLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ (n pd : ℕ) (I : Ideal (𝓞 E)) (l₂ : Level H) (Xo₂ : Moduli Dw l₂) (c₂ : Coeff l₂), c₂.F = c.F → l.Dvd l₂ → l₂.M = l.M * pd → pd.Coprime l.M → l₂.Mb = l.Mb * I → I ⊔ I.map (H.bar : 𝓞 E →+* 𝓞 E) = ⊤ → ∃ d : DeltaDat Xo c n, d.pd = pd ∧ d.I = I ∧ d.l₂ = l₂ ∧ HEq d.Xo₂ Xo₂ ∧ HEq d.c₂ c₂ ∧ d.cδ = 1 ∧ d.IsLev ∧ ∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂ := by
  intro E _ _ _ H Dw l Xo c hr n pd I l₂ Xo₂ c₂ hF hd hM hcop hMb hI
  have hL := GlobalTheory.firstFiveLaws.1
  obtain ⟨r, jK, m, -, -, he, heA, -, hrF⟩ := (GlobalTheory.T.moduliScheme_levelMaps_heckePoints'.2 E H Dw hr).1 l l₂ Xo Xo₂ hd
  obtain ⟨rF, h₁, h₂, hfin, -, hsur, -⟩ := hrF c c₂ hF.symm
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab hL E H Dw l₂ Xo₂ c₂
  let d : DeltaDat Xo c n :=
    { pd := pd, I := I, l₂ := l₂, Xo₂ := Xo₂, c₂ := c₂, hF := hF, r := r, m := m, nab₂ := nab, cδ := 1,
      φδ := fun _ => 1 }
  have hdiv : l₂.M / l.M = pd := by
    rw [hM]; exact Nat.mul_div_cancel_left _ (by have := l.three_le; omega)
  refine ⟨d, rfl, rfl, rfl, HEq.rfl, HEq.rfl, rfl, ⟨hd, hM, hcop, hMb, hI, ⟨?_, heA⟩, ?_,
    one_mem_sec_zero Xo₂ c₂, ?_⟩, st, hnab⟩
  · rw [hdiv] at he; exact he
  · intro k _ _ _ i₂ hk y
    obtain ⟨x₂, hx, hs⟩ := @exists_point_over E _ _ _ H Dw l l₂ Xo c Xo₂ c₂ hF.symm r rF hfin hsur h₁ h₂
      k _ _ _ i₂ hk y.x y.x_over
    obtain ⟨y₂, -, hy⟩ := (GlobalTheory.T.framedPoints_lift_to_levelCover hL E H Dw l Xo c n d).1 k hk y x₂ hx hs
    exact ⟨y₂, hy⟩
  · intro k _ _ _ y₂
    have h := GlobalTheory.Frames.allTest_of_secBaseChange hL.secBaseChange E H Dw l₂ Xo₂ c₂ k y₂
    have e : evR d.Xo₂ d.c₂ d.cδ y₂ = 1 := evalAt_one _ _ y₂ h
    rw [e]; exact one_ne_zero

end GlobalTheory.LevelCover
