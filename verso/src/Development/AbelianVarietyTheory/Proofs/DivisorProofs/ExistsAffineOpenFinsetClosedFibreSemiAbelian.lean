import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSectionOfSmoothClosedFibreStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineOpenDescendingFiniteFreeBaseChangeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenTranslationsMovingClosedPointsIntoOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateBaseChangeAffineOpenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

/- English proof (translation)
Introduce `R _ _ _ hR G _ _ hG s hs`. Use `haveI : IsNoetherianRing R := hR.1`. Use `haveI : QuasiCompact G.hom := hG.quasiCompact`. Use `haveI : IsSeparated G.hom := hG.separated`. Use `haveI : Smooth G.hom := hG.smooth`.

Use `haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom`. Break down `s.eq_empty_or_nonempty with hs0 | ⟨x₀, hx₀⟩` into its components or cases. Conclude with `⟨⊥, isAffineOpen_bot _, by simp [hs0]⟩`. Establish `hcl : ∀ x : G.left, ∃ y ∈ closure ({x} : Set G.left), IsClosed ({y} : Set G.left)` using `fun x => isClosed_closure.exists_closed_singleton ⟨x, subset_closure rfl⟩`. Use `choose f hfx hfc using hcl`.

Establish `hsp : ∀ x, x ⤳ f x` using `fun x => specializes_iff_mem_closure.2 (hfx x)`. Establish `hcp : IsClosed ({closedPoint R} : Set (Sp R))` using `isClosed_singleton_closedPoint R`. Establish `hfib : ∀ x ∈ s, G.hom (f x) = closedPoint R`. Introduce `x hx`. Establish `h1 : G.hom x ⤳ G.hom (f x)` using `(hsp x).map G.hom.continuous`.

Rewrite `h1` using `[hs x hx]`. Establish `h2` using `specializes_iff_mem_closure.1 h1`. Conclude with `closure_minimal (subset_refl _) hcp h2`. Set `s' : Finset G.left` to `s.image f`. Establish `hs' : ∀ y ∈ s', G.hom y = closedPoint R ∧ IsClosed ({y} : Set G.left)`.

Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `⟨hfib x hx, hfc x⟩`. It suffices to establish `H : ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ y ∈ s', y ∈ O by`. Take `⟨O, hO, hyO⟩` from `H`.

Conclude with `⟨O, hO, fun x hx => (hsp x).mem_open O.2 (hyO _ (Finset.mem_image_of_mem f hx))⟩`. Take `⟨V, hV, hxV, -⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens) (show x₀ ∈ (⊤ : G.left.Opens) from trivial)`. Take `⟨O, ⟨u, huO, hu⟩, hmove⟩` from `GlobalTheory.T.exists_open_translations_moving_closedPoints_into_open R G hG V ⟨x₀, hxV, hs x₀ hx₀⟩ s' hs'`. Take `⟨R₁, _, _, _, ρ, a, hfin, het, ha, haO⟩` from `GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR G hG.smooth O ⟨u, huO, hu⟩`. Use `letI : Algebra R R₁ := ρ.toAlgebra`.

Use `haveI : Module.Finite R R₁ := hfin.2.2`. Use `haveI : Algebra.Etale R R₁ := het`. Use `haveI : Module.Flat R R₁ := inferInstance`. Use `haveI : Module.Free R R₁ := Module.free_of_flat_of_isLocalRing`. Set `A : Over.mk (spMap ρ) ⟶ G` to `Over.homMk a ha`.

Take `⟨W, hW, hzW⟩` from `GlobalTheory.T.exists_affineOpen_translate_baseChange R R₁ ρ G V hV A`. Establish `hpb : IsPullback (pullback.fst G.hom (spMap ρ)) (pullback.snd G.hom (spMap ρ)) G.hom (spMap (algebraMap R R₁))` using `IsPullback.of_hasPullback G.hom (spMap ρ)`. Use `GlobalTheory.T.exists_affineOpen_descending_finiteFreeBaseChange R R₁ G.left (pullback G.hom (spMap ρ)) G.hom (pullback.snd _ _) (pullback.fst _ _) hpb inferInstance inferInstance W hW s' ?_` and prove the remaining obligations. Introduce `z hz`. Set `Ω` to `(pullback G.hom (spMap ρ)).residueField z`.

Set `z' : Sp Ω ⟶ pullback G.hom (spMap ρ)` to `(pullback G.hom (spMap ρ)).fromSpecResidueField z`. Establish `hz' : ∀ w, z' w = z` using `fun w => Scheme.fromSpecResidueField_apply z w`. Set `t : Sp Ω ⟶ Sp R` to `z' ≫ pullback.fst _ _ ≫ G.hom`. Set `x : Over.mk t ⟶ G` to `Over.homMk (z' ≫ pullback.fst _ _) (by simp [t])`. Set `a' : Over.mk t ⟶ G` to `Over.homMk (z' ≫ pullback.snd _ _ ≫ a) (by simp only [t, Over.mk_hom, Category.assoc, ha, pullback.condition])`.

Establish `hx : ∀ w, x.left w ∈ s'`. Introduce `w`. Use `show (z' ≫ pullback.fst _ _) w ∈ s'`. Rewrite using `[Scheme.Hom.comp_apply, hz']`. Conclude with `hz`.

Establish `ha' : ∀ w, a'.left w ∈ O`. Introduce `w`. Use `show (z' ≫ pullback.snd _ _ ≫ a) w ∈ O`. Rewrite using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Conclude with `haO ⟨_, rfl⟩`.

Establish `hV'` using `hmove Ω t x a' hx ha'`. Use `hzW Ω z' t x a' rfl rfl hV' (closedPoint Ω)` as an intermediate fact. Use `first`. Consider the case `exact (Scheme.fromSpecResidueField_apply z _) ▸ this`. Consider the case `simpa only [hz'] using this`.

Consider the case `(convert this using 1; exact (hz' _).symm)`.
-/
theorem exists_affine_open_of_finset_closedFibre :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ s : Finset G.left,
    (∀ x ∈ s, G.hom x = closedPoint R) → ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ x ∈ s, x ∈ O := by
  intro R _ _ _ hR G _ _ hG s hs
  haveI : IsNoetherianRing R := hR.1
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : IsSeparated G.hom := hG.separated
  haveI : Smooth G.hom := hG.smooth
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom

  rcases s.eq_empty_or_nonempty with hs0 | ⟨x₀, hx₀⟩
  · exact ⟨⊥, isAffineOpen_bot _, by simp [hs0]⟩

  have hcl : ∀ x : G.left, ∃ y ∈ closure ({x} : Set G.left), IsClosed ({y} : Set G.left) :=
    fun x => isClosed_closure.exists_closed_singleton ⟨x, subset_closure rfl⟩
  choose f hfx hfc using hcl
  have hsp : ∀ x, x ⤳ f x := fun x => specializes_iff_mem_closure.2 (hfx x)
  have hcp : IsClosed ({closedPoint R} : Set (Sp R)) := isClosed_singleton_closedPoint R
  have hfib : ∀ x ∈ s, G.hom (f x) = closedPoint R := by
    intro x hx
    have h1 : G.hom x ⤳ G.hom (f x) := (hsp x).map G.hom.continuous
    rw [hs x hx] at h1
    have h2 := specializes_iff_mem_closure.1 h1
    exact closure_minimal (subset_refl _) hcp h2
  classical
  let s' : Finset G.left := s.image f
  have hs' : ∀ y ∈ s', G.hom y = closedPoint R ∧ IsClosed ({y} : Set G.left) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨hfib x hx, hfc x⟩
  suffices H : ∃ O : G.left.Opens, IsAffineOpen O ∧ ∀ y ∈ s', y ∈ O by
    obtain ⟨O, hO, hyO⟩ := H
    exact ⟨O, hO, fun x hx => (hsp x).mem_open O.2 (hyO _ (Finset.mem_image_of_mem f hx))⟩

  obtain ⟨V, hV, hxV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp G.left.isBasis_affineOpens)
    (show x₀ ∈ (⊤ : G.left.Opens) from trivial)

  obtain ⟨O, ⟨u, huO, hu⟩, hmove⟩ :=
    GlobalTheory.T.exists_open_translations_moving_closedPoints_into_open R G hG V ⟨x₀, hxV, hs x₀ hx₀⟩ s' hs'

  obtain ⟨R₁, _, _, _, ρ, a, hfin, het, ha, haO⟩ :=
    GlobalTheory.T.exists_finiteEtale_section_of_smooth_closedFibre R hR G hG.smooth O ⟨u, huO, hu⟩
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Finite R R₁ := hfin.2.2
  haveI : Algebra.Etale R R₁ := het
  haveI : Module.Flat R R₁ := inferInstance
  haveI : Module.Free R R₁ := Module.free_of_flat_of_isLocalRing

  let A : Over.mk (spMap ρ) ⟶ G := Over.homMk a ha
  obtain ⟨W, hW, hzW⟩ := GlobalTheory.T.exists_affineOpen_translate_baseChange R R₁ ρ G V hV A

  have hpb : IsPullback (pullback.fst G.hom (spMap ρ)) (pullback.snd G.hom (spMap ρ)) G.hom
      (spMap (algebraMap R R₁)) := IsPullback.of_hasPullback G.hom (spMap ρ)
  refine GlobalTheory.T.exists_affineOpen_descending_finiteFreeBaseChange R R₁ G.left (pullback G.hom (spMap ρ)) G.hom (pullback.snd _ _) (pullback.fst _ _)
    hpb inferInstance inferInstance W hW s' ?_
  intro z hz
  let Ω := (pullback G.hom (spMap ρ)).residueField z
  let z' : Sp Ω ⟶ pullback G.hom (spMap ρ) := (pullback G.hom (spMap ρ)).fromSpecResidueField z
  have hz' : ∀ w, z' w = z := fun w => Scheme.fromSpecResidueField_apply z w
  let t : Sp Ω ⟶ Sp R := z' ≫ pullback.fst _ _ ≫ G.hom
  let x : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.fst _ _) (by simp [t])
  let a' : Over.mk t ⟶ G := Over.homMk (z' ≫ pullback.snd _ _ ≫ a)
    (by simp only [t, Over.mk_hom, Category.assoc, ha, pullback.condition])
  have hx : ∀ w, x.left w ∈ s' := by
    intro w
    show (z' ≫ pullback.fst _ _) w ∈ s'
    rw [Scheme.Hom.comp_apply, hz']
    exact hz
  have ha' : ∀ w, a'.left w ∈ O := by
    intro w
    show (z' ≫ pullback.snd _ _ ≫ a) w ∈ O
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact haO ⟨_, rfl⟩
  have hV' := hmove Ω t x a' hx ha'
  have := hzW Ω z' t x a' rfl rfl hV' (closedPoint Ω)
  first
    | exact (Scheme.fromSpecResidueField_apply z _) ▸ this
    | simpa only [hz'] using this
    | (convert this using 1; exact (hz' _).symm)

end GlobalTheory.Mum
