import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.TopAmpExists
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ArcFamSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleOfAmpleGeometricFibresAbelianScheme
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models GlobalTheory.ZM

namespace GlobalTheory.AmpleGlobal

/- English proof (translation)
Take `⟨z, -, hz⟩` from `Scheme.Pullback.exists_preimage_pullback q a h`. Use `⟨(pullback f x).residueField z, inferInstance, (Spec.preimage ((pullback f x).fromSpecResidueField z ≫ pullback.snd f x)).hom, (pullback f x).fromSpecResidueField z ≫ pullback.fst f x, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = Spec.map (CommRingCat.ofHom _) ≫ x`. Rewrite using `[CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, Category.assoc, pullback.condition]`.
-/
theorem exists_lift_fieldExtension {S S' : Scheme.{0}} (f : S' ⟶ S) {K₀ : Type} [Field K₀] (x : Sp K₀ ⟶ S)
    (a : Sp K₀) (q : S') (h : f q = x a) :
    ∃ (K : Type) (_ : Field K) (i : K₀ →+* K) (u : Sp K ⟶ S'), u ≫ f = spMap i ≫ x := by
  obtain ⟨z, -, hz⟩ := Scheme.Pullback.exists_preimage_pullback q a h
  refine ⟨(pullback f x).residueField z, inferInstance,
    (Spec.preimage ((pullback f x).fromSpecResidueField z ≫ pullback.snd f x)).hom,
    (pullback f x).fromSpecResidueField z ≫ pullback.fst f x, ?_⟩
  change _ = Spec.map (CommRingCat.ofHom _) ≫ x
  rw [CommRingCat.ofHom_hom, Spec.map_preimage, Category.assoc, Category.assoc, pullback.condition]

/- English proof (translation)
Use `GlobalTheory.AmpleLocal.relAmple_of_locally S G M hM inferInstance inferInstance (fun s => ?_)` and prove the remaining obligations. Apply the tactic sequence `obtain ⟨V, hV, hsV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (by first | exact AlgebraicGeometry.isBasis_affine_open S | exact S.isBasis_affineOpens | exact AlgebraicGeometry.Scheme.isBasis_affineOpens S | exact isBasis_affineOpens S)) (show s ∈ (⊤ : S.Opens) from trivia …`. Establish `hV' : IsAffineOpen V` using `hV`. Establish `: IsNoetherianRing Γ(S, V)` using `IsLocallyNoetherian.component_noetherian ⟨V, hV'⟩`. Set `y : Spec (CommRingCat.of Γ(S, V)) ⟶ S` to `hV'.fromSpec`.

Set `q` to `hV'.primeIdealOf ⟨s, hsV⟩`. Establish `hq : hV'.fromSpec q = s` using `hV'.fromSpec_primeIdealOf ⟨s, hsV⟩`. Set `g : Γ(S, V) →+* q.asIdeal.ResidueField` to `algebraMap _ _`. Set `B : Over (Spec (CommRingCat.of Γ(S, V)))` to `Over.mk (pullback.snd G.hom y)`. Establish `hB : IsPullback (pullback.fst G.hom y) B.hom G.hom y` using `IsPullback.of_hasPullback _ _`.

Establish `hLB : (M.pull (pullback.fst G.hom y)).IsLB` using `pull_isLB hM _`. Apply the tactic sequence `have hflat : Flat B.hom := by first | (show Flat (pullback.snd G.hom y); infer_instance) | exact MorphismProperty.pullback_snd _ _ inferInstance`. Establish `hprojB` using `(GlobalTheory.ProjSpace.isProjBy_iff_isProjOver _).2 (hproj _ y B _ hB)`. Establish `hfib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom g))).obj B) ((M.pull (pullback.fst G.hom y)).pull (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g))))`. Take `⟨S', f, G', φ, L', hφ, hL', e, ⟨s', hs'⟩, hA'⟩` from `hpt s`.

Set `x : Sp q.asIdeal.ResidueField ⟶ S` to `Spec.map (CommRingCat.ofHom g) ≫ y`. Set `a : Sp q.asIdeal.ResidueField` to `IsLocalRing.closedPoint _`. Establish `ha : x a = s`. Establish `hpt' : (Spec.map (CommRingCat.ofHom g)) a = q`. Apply `PrimeSpectrum.ext` to reduce the goal to its premises.

Express the relevant statement in the definitionally equal form `Ideal.comap g (IsLocalRing.maximalIdeal _) = q.asIdeal`. Rewrite using `[IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]`. Use `first`. Consider the case `(show y ((Spec.map (CommRingCat.ofHom g)) a) = s`. Rewrite using `[hpt']`.

Conclude with `hq)`. Consider the case `exact (Scheme.comp_base_apply _ _ _).trans (by rw [hpt']; exact hq)`. Take `⟨K, _, i, u, hu⟩` from `exists_lift_fieldExtension f x a s' (hs'.trans ha.symm)`. Establish `h₂ : IsPullback (pullback.fst G.hom (spMap i ≫ x)) (pullback.snd G.hom (spMap i ≫ x)) G.hom (spMap i ≫ x)` using `IsPullback.of_hasPullback _ _`. Establish `hA₂` using `GlobalTheory.FibreAmple.relAmple_of_factor hM hφ h₂ u hu hL' e hA'`.

Conclude with `GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i ((IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom g))).paste_horiz hB) h₂ (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA₂`. Take `⟨r, hr, hA⟩` from `GlobalTheory.AmpleNear.relAmple_near_fibre Γ(S, V) B (M.pull (pullback.fst G.hom y)) hflat hprojB hLB q.asIdeal.ResidueField g (GlobalTheory.FibreAmple.residueField_fraction q.asIdeal) hfib`. Set `U₀ : (Spec (CommRingCat.of Γ(S, V))).Opens` to `PrimeSpectrum.basicOpen r`. Set `j` to `U₀.ι`. Establish `: IsOpenImmersion y` using `by dsimp only [y]; infer_instance`.

Establish `: IsOpenImmersion j` using `by dsimp only [j]; exact inferInstance`. Establish `hqr : q ∈ PrimeSpectrum.basicOpen r` using `(PrimeSpectrum.mem_basicOpen _ _).2 fun h => hr ((Ideal.algebraMap_residueField_eq_zero).2 h)`. Use `⟨(j ≫ y).opensRange, ⟨⟨q, hqr⟩, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hq]`. Both sides reduce to the same expression.

Establish `hu : (j ≫ y).isoOpensRange.inv ≫ (j ≫ y) = (j ≫ y).opensRange.ι`. Rewrite using `[Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]`. Conclude with `GlobalTheory.FibreAmple.relAmple_of_factor hM ((IsPullback.of_hasPullback B.hom j).paste_horiz hB) (isPullback_morphismRestrict G.hom _).flip _ hu (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA`.
-/
theorem relAmple_of_pointwise {S : Scheme.{0}} [IsLocallyNoetherian S] (G : Over S) [IsProper G.hom] [Flat G.hom]
    (M : LB G.left) (hM : M.IsLB)
    (hproj : ∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ G.left),
      IsPullback φ B.hom G.hom y → IsProjOver B.hom)
    (hpt : ∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (G' : Over S') (φ : G'.left ⟶ G.left) (L' : LB G'.left),
      IsPullback φ G'.hom G.hom f ∧ L'.IsLB ∧ LBIso L' (M.pull φ) ∧ p ∈ Set.range f ∧ Out.RelAmple G' L') :
    Out.RelAmple G M := by
  refine GlobalTheory.AmpleLocal.relAmple_of_locally S G M hM inferInstance inferInstance (fun s => ?_)
  obtain ⟨V, hV, hsV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (by first | exact AlgebraicGeometry.isBasis_affine_open S | exact S.isBasis_affineOpens | exact AlgebraicGeometry.Scheme.isBasis_affineOpens S | exact isBasis_affineOpens S)) (show s ∈ (⊤ : S.Opens) from trivial)
  have hV' : IsAffineOpen V := hV
  have : IsNoetherianRing Γ(S, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV'⟩
  let y : Spec (CommRingCat.of Γ(S, V)) ⟶ S := hV'.fromSpec
  let q := hV'.primeIdealOf ⟨s, hsV⟩
  have hq : hV'.fromSpec q = s := hV'.fromSpec_primeIdealOf ⟨s, hsV⟩
  let g : Γ(S, V) →+* q.asIdeal.ResidueField := algebraMap _ _
  let B : Over (Spec (CommRingCat.of Γ(S, V))) := Over.mk (pullback.snd G.hom y)
  have hB : IsPullback (pullback.fst G.hom y) B.hom G.hom y := IsPullback.of_hasPullback _ _
  have hLB : (M.pull (pullback.fst G.hom y)).IsLB := pull_isLB hM _
  have hflat : Flat B.hom := by
    first | (show Flat (pullback.snd G.hom y); infer_instance) | exact MorphismProperty.pullback_snd _ _ inferInstance
  have hprojB := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver _).2 (hproj _ y B _ hB)
  have hfib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom g))).obj B)
      ((M.pull (pullback.fst G.hom y)).pull (pullback.fst B.hom (Spec.map (CommRingCat.ofHom g)))) := by
    obtain ⟨S', f, G', φ, L', hφ, hL', e, ⟨s', hs'⟩, hA'⟩ := hpt s
    let x : Sp q.asIdeal.ResidueField ⟶ S := Spec.map (CommRingCat.ofHom g) ≫ y
    let a : Sp q.asIdeal.ResidueField := IsLocalRing.closedPoint _
    have ha : x a = s := by
      have hpt' : (Spec.map (CommRingCat.ofHom g)) a = q := by
        apply PrimeSpectrum.ext
        change Ideal.comap g (IsLocalRing.maximalIdeal _) = q.asIdeal
        rw [IsLocalRing.maximalIdeal_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.ker_algebraMap_residueField]
      first
        | (show y ((Spec.map (CommRingCat.ofHom g)) a) = s
           rw [hpt']
           exact hq)
        | exact (Scheme.comp_base_apply _ _ _).trans (by rw [hpt']; exact hq)
    obtain ⟨K, _, i, u, hu⟩ := exists_lift_fieldExtension f x a s' (hs'.trans ha.symm)
    have h₂ : IsPullback (pullback.fst G.hom (spMap i ≫ x)) (pullback.snd G.hom (spMap i ≫ x)) G.hom
        (spMap i ≫ x) := IsPullback.of_hasPullback _ _
    have hA₂ := GlobalTheory.FibreAmple.relAmple_of_factor hM hφ h₂ u hu hL' e hA'
    exact GlobalTheory.FibreAmple.relAmple_of_fieldExtension hM i
      ((IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom g))).paste_horiz hB) h₂
      (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA₂
  obtain ⟨r, hr, hA⟩ := GlobalTheory.AmpleNear.relAmple_near_fibre Γ(S, V) B (M.pull (pullback.fst G.hom y)) hflat hprojB hLB
    q.asIdeal.ResidueField g (GlobalTheory.FibreAmple.residueField_fraction q.asIdeal) hfib
  let U₀ : (Spec (CommRingCat.of Γ(S, V))).Opens := PrimeSpectrum.basicOpen r
  let j := U₀.ι
  have : IsOpenImmersion y := by dsimp only [y]; infer_instance
  have : IsOpenImmersion j := by dsimp only [j]; exact inferInstance
  have hqr : q ∈ PrimeSpectrum.basicOpen r :=
    (PrimeSpectrum.mem_basicOpen _ _).2 fun h => hr ((Ideal.algebraMap_residueField_eq_zero).2 h)
  refine ⟨(j ≫ y).opensRange, ⟨⟨q, hqr⟩, ?_⟩, ?_⟩
  · rw [← hq]
    rfl
  · have hu : (j ≫ y).isoOpensRange.inv ≫ (j ≫ y) = (j ≫ y).opensRange.ι := by
      rw [Iso.inv_comp_eq, Scheme.Hom.isoOpensRange_hom_ι]
    exact GlobalTheory.FibreAmple.relAmple_of_factor hM ((IsPullback.of_hasPullback B.hom j).paste_horiz hB)
      (isPullback_morphismRestrict G.hom _).flip _ hu (pull_isLB hLB _) (GlobalTheory.FibreAmple.lbIso_pull_pull hM _ _) hA

/- English proof (translation)
Introduce `E _ _ _ H S _ t hP hproj hpt`. Establish `hflat : Flat t.G.hom` using `by first`. Consider the case `exact inferInstance`. Consider the case `(haveI := t.semi.smooth; infer_instance)`. Use `relAmple_of_pointwise t.G t.PP.L t.PP.isLB hproj (fun p => ?_)` and prove the remaining obligations.

Take `⟨S', f, t', m, hp, hA, -⟩` from `hpt p`. Use `⟨S', f, t'.G, m.cm.F, t'.PP.L, m.cart.1, t'.PP.isLB, ?_, hp, hA⟩` and prove the remaining obligations. Use `first`. Consider the case `(obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw⟩)`. Consider the case `(obtain ⟨w, hw⟩ := m.lin; exact ⟨w, hw⟩)`.

Consider the case `(obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw.1⟩)`. Consider the case `(obtain ⟨w, -, hw, -⟩ := m.lin; exact ⟨w, hw⟩)`. Consider the case `(obtain ⟨w, hw, -⟩ := m.lin; exact (hw : False))`.
-/
theorem relAmple_of_polarised_at_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S), IsProper t.G.hom → (∀ (A : Type) [CommRing A] (y : Sp A ⟶ S) (B : Over (Sp A)) (φ : B.left ⟶ t.G.left), IsPullback φ B.hom t.G.hom y → IsProjOver B.hom) → (∀ p : S, ∃ (S' : Scheme.{0}) (f : S' ⟶ S) (t' : SAB H S') (_ : SABMap t' t f), p ∈ Set.range f ∧ Out.RelAmple t'.G t'.PP.L ∧ Out.KTriv t'.G t'.PP.L) → Out.RelAmple t.G t.PP.L := by
  intro E _ _ _ H S _ t hP hproj hpt
  have hflat : Flat t.G.hom := by
    first
      | exact inferInstance
      | (haveI := t.semi.smooth; infer_instance)
  refine relAmple_of_pointwise t.G t.PP.L t.PP.isLB hproj (fun p => ?_)
  obtain ⟨S', f, t', m, hp, hA, -⟩ := hpt p
  refine ⟨S', f, t'.G, m.cm.F, t'.PP.L, m.cart.1, t'.PP.isLB, ?_, hp, hA⟩
  first
    | (obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, -⟩ := m.lin; exact ⟨w, hw.1⟩)
    | (obtain ⟨w, -, hw, -⟩ := m.lin; exact ⟨w, hw⟩)
    | (obtain ⟨w, hw, -⟩ := m.lin; exact (hw : False))

end GlobalTheory.AmpleGlobal
