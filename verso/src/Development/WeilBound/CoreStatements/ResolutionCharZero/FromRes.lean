import Mathlib
import Development.ResolutionOfSingularities.Statements
import Development.WeilBound.CoreStatements.ResolutionCharZero.WeakPair
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromResIso
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromResSnc
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.ResK ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.FromRes

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.ResKSide FunctorialResolution

/- English proof (translation)
Introduce `x`. Take `⟨U, hU, hx, -⟩` from `(Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)`. Use `⟨⟨U, hU⟩, 1, hx, Submonoid.one_mem _, ?_⟩` and prove the remaining obligations. Simplify using `[Ideal.span_singleton_one]`.
-/
theorem isEffectiveCartier_top {X : Scheme.{0}} : IsEffectiveCartier (⊤ : X.IdealSheafData) := by
  intro x
  obtain ⟨U, hU, hx, -⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  refine ⟨⟨U, hU⟩, 1, hx, Submonoid.one_mem _, ?_⟩
  simp [Ideal.span_singleton_one]

/- English proof (translation)
Use `⟨by simpa using (isEffectiveCartier_top (X := Y)), fun T g _ => ⟨g ≫ e.inv, by simp, fun h hh => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hh]`. Simplify using the standard rewrite rules.
-/
theorem isBlowup_iso_top {X Y : Scheme.{0}} (e : Y ≅ X) : IsBlowup e.hom (⊤ : X.IdealSheafData) := by
  refine ⟨by simpa using (isEffectiveCartier_top (X := Y)), fun T g _ => ⟨g ≫ e.inv, by simp, fun h hh => ?_⟩⟩
  rw [← hh]; simp

/- English proof (translation)
The claim follows from `| 0, _ => by have h0 : s.structMap 0 = s.isoZero.hom := by simp only [BlowupSequence.structMap, BlowupSequence.down] have : (homOfLE (Nat.zero_le 0)).op = 𝟙 (op (0 : ℕ)) := Subsingleton.elim _ _ rw [this, CategoryTheory.Functor.map_id, Category.id_comp] rw [h0] simpa using Resolu …`.
-/
theorem isBlowupSeq_structMap {X : Scheme.{0}} (s : BlowupSequence X) :
    ∀ i, i ≤ s.length → Resolution.IsBlowupSeq (s.structMap i)
  | 0, _ => by
    have h0 : s.structMap 0 = s.isoZero.hom := by
      simp only [BlowupSequence.structMap, BlowupSequence.down]
      have : (homOfLE (Nat.zero_le 0)).op = 𝟙 (op (0 : ℕ)) := Subsingleton.elim _ _
      rw [this, CategoryTheory.Functor.map_id, Category.id_comp]
    rw [h0]
    simpa using Resolution.IsBlowupSeq.step ⊤ s.isoZero.hom .id (isBlowup_iso_top s.isoZero)
  | i + 1, hi => by
    have ih := isBlowupSeq_structMap s i (Nat.le_of_succ_le hi)
    rw [← s.structMap_down (Nat.le_succ i)]
    exact .step (s.center i) (s.down (Nat.le_succ i)) ih (s.isBlowup i hi)

/- English proof (translation)
The claim follows from `isBlowupSeq_structMap s s.length le_rfl`.
-/
theorem isBlowupSeq_topMap {X : Scheme.{0}} (s : BlowupSequence X) : Resolution.IsBlowupSeq s.topMap :=
  isBlowupSeq_structMap s s.length le_rfl

/- English proof (translation)
Introduce `K _ _ M D X i U ⟨hi, hred, hdense, hU⟩`. Take `⟨R, hR, -, -⟩` from `H`. Establish `: IsProper (PSpace.str K M)` using `isProper_str K M`. Set `f : X ⟶ Spec (CommRingCat.of K)` to `i ≫ PSpace.str K M`. Establish `: LocallyOfFiniteType f` using `by dsimp [f]; infer_instance`.

Establish `: QuasiCompact f` using `by dsimp [f]; infer_instance`. Take `⟨hsm, -, hiso, hd, -, -⟩` from `hR K X f`. Establish `hproj : IsProjOver f` using `⟨M, i, hi, rfl⟩`. Use `⟨_, (R K X f).topMap, (isBlowupSeq_topMap (R K X f)).isProjOver hproj, hsm, ?_, ?_⟩` and prove the remaining obligations. Establish `: Smooth (U.ι ≫ f)` using `hU.smooth D _`.

Conclude with `isIso_morphismRestrict_of_le _ (le_smoothLocus f U)`. Conclude with `dense_preimage (R K X f).topMap (V := f.smoothLocus) hd hdense`.
-/
theorem resW_of_functorialResolution (H : FunctorialResolutionCharZero.{0}) : ResW := by
  intro K _ _ M D X i U ⟨hi, hred, hdense, hU⟩
  obtain ⟨R, hR, -, -⟩ := H
  have : IsProper (PSpace.str K M) := isProper_str K M
  let f : X ⟶ Spec (CommRingCat.of K) := i ≫ PSpace.str K M
  have : LocallyOfFiniteType f := by dsimp [f]; infer_instance
  have : QuasiCompact f := by dsimp [f]; infer_instance
  obtain ⟨hsm, -, hiso, hd, -, -⟩ := hR K X f
  have hproj : IsProjOver f := ⟨M, i, hi, rfl⟩
  refine ⟨_, (R K X f).topMap, (isBlowupSeq_topMap (R K X f)).isProjOver hproj, hsm, ?_, ?_⟩
  · have : Smooth (U.ι ≫ f) := hU.smooth D _
    exact isIso_morphismRestrict_of_le _ (le_smoothLocus f U)
  · exact dense_preimage (R K X f).topMap (V := f.smoothLocus) hd hdense

/- English proof (translation)
Establish `h` using `EmbeddedResolution.inStrictNormalCrossingPosition_nil p`. Use `⟨by simp, fun x => ?_⟩` and prove the remaining obligations. Take `⟨U, hx, m, c, a, h1, h2, h3⟩` from `h.2 x`. Conclude with `⟨U, hx, m, c.map, c.comp_struct, c.isEtale, a, h1, h2, h3⟩`.
-/
theorem hasSimpleNormalCrossings_nil {X : Scheme.{0}} {k : Type} [Field k] (p : X ⟶ Spec (CommRingCat.of k))
    [Smooth p] : HasSimpleNormalCrossings p ([] : List X.IdealSheafData) := by
  have h := EmbeddedResolution.inStrictNormalCrossingPosition_nil p
  refine ⟨by simp, fun x => ?_⟩
  obtain ⟨U, hx, m, c, a, h1, h2, h3⟩ := h.2 x
  exact ⟨U, hx, m, c.map, c.comp_struct, c.isEtale, a, h1, h2, h3⟩

/- English proof (translation)
Introduce `K _ _ d X g hd hp U hU`. Take `⟨R, hR, -, -⟩` from `H`. Establish `hP : IsProper g` using `isProper_of_isProjOver hp`. Establish `: Smooth g` using `hd.smooth d _`. Establish `: CompactSpace X` using `QuasiCompact.compactSpace_of_compactSpace g`.

Establish `: IsLocallyNoetherian X` using `LocallyOfFiniteType.isLocallyNoetherian g`. Apply the tactic sequence `have : IsNoetherian X := by first | infer_instance | exact ⟨⟩`. Establish `: NoetherianSpace X` using `inferInstance`. Set `I : X.IdealSheafData` to `Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩`. Establish `hsupp : I.support = ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩` using `SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal _)`.

Establish `hdense : Dense (I.support : Set X)ᶜ` using `by rw [hsupp]; simpa using hU`. Establish `hI : IsNonzeroOnComponents I` using `SncBlowup.not_subset_of_dense_compl hdense`. Establish `hs` using `hR K X g I hI [] (hasSimpleNormalCrossings_nil g)`. Use `set s := R K X g I hI [] (hasSimpleNormalCrossings_nil g) with hsdef`. Establish `hsm : Smooth (s.topMap ≫ g)`.

Take `⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩` from `hs`. Conclude with `h s.length le_rfl`. Establish `hUc : I.support.compl = U`. Use extensionality with `x`. Simplify using `[hsupp]`.

Establish `hiso` using `isIso_topMap_restrict_of_isPrincipalizingSequence hs`. Rewrite `hiso` using `[hUc]`. Establish `hsnc` using `isStrictNormalCrossings_of_isPrincipalizingSequence_nil hs`. Rewrite `hsnc` using `[hsupp]`. Conclude with `⟨_, s.topMap, (isBlowupSeq_topMap s).isProjOver hp, hsm, hiso, hsnc⟩`.
-/
theorem princW_of_functorialPrincipalization (H : FunctorialPrincipalizationCharZero.{0}) : PrincW := by
  intro K _ _ d X g hd hp U hU
  obtain ⟨R, hR, -, -⟩ := H
  have hP : IsProper g := isProper_of_isProjOver hp
  have : Smooth g := hd.smooth d _
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : IsNoetherian X := by first | infer_instance | exact ⟨⟩
  have : NoetherianSpace X := inferInstance
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩
  have hsupp : I.support = ⟨(U : Set X)ᶜ, U.isOpen.isClosed_compl⟩ :=
    SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal _)
  have hdense : Dense (I.support : Set X)ᶜ := by rw [hsupp]; simpa using hU
  have hI : IsNonzeroOnComponents I := SncBlowup.not_subset_of_dense_compl hdense
  have hs := hR K X g I hI [] (hasSimpleNormalCrossings_nil g)
  set s := R K X g I hI [] (hasSimpleNormalCrossings_nil g) with hsdef
  have hsm : Smooth (s.topMap ≫ g) := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hs
    exact h s.length le_rfl
  have hUc : I.support.compl = U := by
    ext x; simp [hsupp]
  have hiso := isIso_topMap_restrict_of_isPrincipalizingSequence hs
  rw [hUc] at hiso
  have hsnc := isStrictNormalCrossings_of_isPrincipalizingSequence_nil hs
  rw [hsupp] at hsnc
  exact ⟨_, s.topMap, (isBlowupSeq_topMap s).isProjOver hp, hsm, hiso, hsnc⟩

end PositivityTheory.ResPlug.FromRes
