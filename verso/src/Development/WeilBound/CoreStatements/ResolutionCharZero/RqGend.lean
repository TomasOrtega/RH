import Mathlib
import Development.WeilBound.CoreStatements.ResolutionCharZero.PrincipalisationCharZeroBotOfEff
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromResIso
import Development.WeilBound.CoreStatements.ResolutionCharZero.FromResSnc

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace PositivityTheory.ResPlug.GEndGen

open GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.SncBlowup FunctorialResolution PositivityTheory.ResPlug.WeightsCompactStabilizer PositivityTheory.ResPlug.FromRes

/- English proof (translation)
The claim follows from `h`.
-/
theorem effCartier_of {X : Scheme.{0}} {J : X.IdealSheafData} (h : Blowup.IsLocallyGeneratedByNonZeroDivisor J) :
    FinalTheorems.EffCartier J := h

/- English proof (translation)
Introduce `x`. Take `⟨U, a, hxU, ha, hAU⟩` from `hA x`. Take `⟨V, b, hxV, hb, hBV⟩` from `hB x`. Take `⟨f, g, hfg, hxf⟩` from `exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩`. Establish `hWU : Y.affineBasicOpen f ≤ U` using `Y.basicOpen_le f`.

Establish `hle : Y.basicOpen f ≤ Y.basicOpen g` using `hfg.le`. Establish `hWV : Y.affineBasicOpen f ≤ V` using `hle.trans (Y.basicOpen_le g)`. Establish `eA` using `A.map_ideal hWU`. Establish `eB` using `B.map_ideal hWV`. Rewrite `eA` using `[hAU, Ideal.map_span, Set.image_singleton]`.

Rewrite `eB` using `[hBV, Ideal.map_span, Set.image_singleton]`. Establish `ha' : (Y.presheaf.map (homOfLE hWU).op).hom a ∈ nonZeroDivisors Γ(Y, Y.basicOpen f)`. Use `U.2.isLocalization_basicOpen f` as an intermediate fact. Conclude with `IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers f) Γ(Y, Y.basicOpen f) ha`. Establish `hb1 : (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom b ∈ nonZeroDivisors Γ(Y, Y.basicOpen g)`.

Use `V.2.isLocalization_basicOpen g` as an intermediate fact. Conclude with `IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers g) Γ(Y, Y.basicOpen g) hb`. Establish `hiso : IsIso (Y.presheaf.map (homOfLE hle).op)`. Establish `: (homOfLE hle).op = eqToHom (by rw [hfg])` using `Subsingleton.elim _ _`. Rewrite using `[this]`.

Use `infer_instance`. Establish `hb' : (Y.presheaf.map (homOfLE hWV).op).hom b ∈ nonZeroDivisors Γ(Y, Y.basicOpen f)`. Establish `e : (Y.presheaf.map (homOfLE hWV).op).hom b = (Y.presheaf.map (homOfLE hle).op).hom ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom b)`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso (asIso (Y.presheaf.map (homOfLE hle).op)) hb1`. Use `⟨Y.affineBasicOpen f, (Y.presheaf.map (homOfLE hWU).op).hom a * (Y.presheaf.map (homOfLE hWV).op).hom b, hxf, mul_mem ha' hb', ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ← eA, ← eB, Ideal.span_singleton_mul_span_singleton]`. Both sides reduce to the same expression.
-/
theorem isLocallyGeneratedByNonZeroDivisor_mul {Y : Scheme.{0}} {A B : Y.IdealSheafData}
    (hA : Blowup.IsLocallyGeneratedByNonZeroDivisor A) (hB : Blowup.IsLocallyGeneratedByNonZeroDivisor B) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor (A * B) := by
  intro x
  obtain ⟨U, a, hxU, ha, hAU⟩ := hA x
  obtain ⟨V, b, hxV, hb, hBV⟩ := hB x
  obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 x ⟨hxU, hxV⟩
  have hWU : Y.affineBasicOpen f ≤ U := Y.basicOpen_le f
  have hle : Y.basicOpen f ≤ Y.basicOpen g := hfg.le
  have hWV : Y.affineBasicOpen f ≤ V := hle.trans (Y.basicOpen_le g)
  have eA := A.map_ideal hWU
  have eB := B.map_ideal hWV
  rw [hAU, Ideal.map_span, Set.image_singleton] at eA
  rw [hBV, Ideal.map_span, Set.image_singleton] at eB
  have ha' : (Y.presheaf.map (homOfLE hWU).op).hom a ∈ nonZeroDivisors Γ(Y, Y.basicOpen f) := by
    have := U.2.isLocalization_basicOpen f
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers f) Γ(Y, Y.basicOpen f) ha
  have hb1 : (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom b ∈ nonZeroDivisors Γ(Y, Y.basicOpen g) := by
    have := V.2.isLocalization_basicOpen g
    exact IsLocalization.nonZeroDivisors_le_comap (Submonoid.powers g) Γ(Y, Y.basicOpen g) hb
  have hiso : IsIso (Y.presheaf.map (homOfLE hle).op) := by
    have : (homOfLE hle).op = eqToHom (by rw [hfg]) := Subsingleton.elim _ _
    rw [this]; infer_instance
  have hb' : (Y.presheaf.map (homOfLE hWV).op).hom b ∈ nonZeroDivisors Γ(Y, Y.basicOpen f) := by
    have e : (Y.presheaf.map (homOfLE hWV).op).hom b = (Y.presheaf.map (homOfLE hle).op).hom
        ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom b) := by
      rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl
    rw [e]
    exact FunctorialResolution.Blowup.map_mem_nonZeroDivisors_of_iso (asIso (Y.presheaf.map (homOfLE hle).op)) hb1
  refine ⟨Y.affineBasicOpen f, (Y.presheaf.map (homOfLE hWU).op).hom a * (Y.presheaf.map (homOfLE hWV).op).hom b,
    hxf, mul_mem ha' hb', ?_⟩
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, ← eA, ← eB, Ideal.span_singleton_mul_span_singleton]
  rfl

/- English proof (translation)
Introduce `x`. Take `⟨U, f, hxU, -, hJU⟩` from `hJ (π.base x)`. Take `⟨V, hV, hxV, hVle⟩` from `(Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens) (show x ∈ π ⁻¹ᵁ (U : X.Opens) from hxU)`. Use `⟨⟨V, hV⟩, (π.appLE (U : X.Opens) V hVle).hom f, hxV, ?_⟩` and prove the remaining obligations. Rewrite using `[Scheme.IdealSheafData.comap_ideal_eq_map_appLE J π U ⟨V, hV⟩ hVle, hJU, Ideal.map_span, Set.image_singleton]`.
-/
theorem exists_span_singleton_comap {X X' : Scheme.{0}} (π : X' ⟶ X) {J : X.IdealSheafData}
    (hJ : Blowup.IsLocallyGeneratedByNonZeroDivisor J) :
    ∀ x : X', ∃ (U : X'.affineOpens) (f : Γ(X', U.1)), x ∈ U.1 ∧ (J.comap π).ideal U = Ideal.span {f} := by
  intro x
  obtain ⟨U, f, hxU, -, hJU⟩ := hJ (π.base x)
  obtain ⟨V, hV, hxV, hVle⟩ := (Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens)
    (show x ∈ π ⁻¹ᵁ (U : X.Opens) from hxU)
  refine ⟨⟨V, hV⟩, (π.appLE (U : X.Opens) V hVle).hom f, hxV, ?_⟩
  rw [Scheme.IdealSheafData.comap_ideal_eq_map_appLE J π U ⟨V, hV⟩ hVle, hJU, Ideal.map_span, Set.image_singleton]

/- English proof (translation)
Introduce `x`. Take `⟨U, f, hxU, hFU⟩` from `hF x`. Use `⟨U, f, hxU, ?_, hFU⟩` and prove the remaining obligations. Establish `hsupp : ∀ z (hz : z ∈ U.1), Y.presheaf.germ U.1 z hz f = 0 → z ∈ F.support`. Introduce `z hz h0`.

Rewrite using `[EmbeddedResolution.mem_support_iff_stalkIdeal_ne_top, EmbeddedResolution.stalkIdeal_eq_map_germ F z U hz, hFU, Ideal.map_span, Set.image_singleton]`. Introduce `htop`. Establish `h1 : (Y.presheaf.germ U.1 z hz).hom f = 0` using `h0`. Rewrite `htop` using `[h1, Ideal.span_singleton_eq_top]`. Conclude with `not_isUnit_zero htop`.

Establish `hgerm : ∀ y (hy : y ∈ U.1), Y.presheaf.germ U.1 y hy f ≠ 0`. Introduce `y hy h0`. Take `⟨W, hyW, i1, i2, hW⟩` from `TopCat.Presheaf.germ_eq Y.presheaf y hy hy f 0 (by rw [h0, map_zero])`. Establish `hWs : ∀ z ∈ W, z ∈ F.support`. Introduce `z hzW`.

Use `hsupp z (i1.le hzW) ?_` and prove the remaining obligations. Rewrite using `[← Y.presheaf.germ_res_apply i1 z hzW f, hW, map_zero, map_zero]`. Take `⟨C, hC, hyC⟩` from `exists_mem_irreducibleComponents_subset_of_isIrreducible ({y} : Set Y) isIrreducible_singleton`. Establish `hnC` using `hnz C hC`. Take `⟨z, hzC, hz⟩` from `Set.not_subset.mp hnC`.

Take `⟨w, hwC, hw1, hw2⟩` from `hC.1.2 ((F.support : Set Y)ᶜ) (W : Set Y) F.support.2.isOpen_compl W.2 ⟨z, hzC, hz⟩ ⟨y, hyC rfl, hyW⟩`. Conclude with `hw1 (hWs w hw2)`. Establish `key : ∀ g : Γ(Y, U.1), f * g = 0 → g = 0`. Introduce `g hg`. Apply `TopCat.Presheaf.section_ext Y.sheaf U.1 g 0` to reduce the goal to its premises.

Introduce `y hy`. Use `EmbeddedResolution.isDomain_stalk_of_smooth q y` as an intermediate fact. Establish `h2 : Y.presheaf.germ U.1 y hy f * Y.presheaf.germ U.1 y hy g = 0`. Rewrite using `[← map_mul, hg, map_zero]`. Rewrite using `[map_zero]`.

Conclude with `(mul_eq_zero.mp h2).resolve_left (hgerm y hy)`. Rewrite using `[mem_nonZeroDivisors_iff]`. Conclude with `⟨key, fun g hg => key g (by rw [mul_comm]; exact hg)⟩`.
-/
theorem isLocallyGeneratedByNonZeroDivisor_of_span_singleton {k : Type} [Field k] {Y : Scheme.{0}}
    (q : Y ⟶ Spec (CommRingCat.of k)) [Smooth q] {F : Y.IdealSheafData}
    (hF : ∀ x : Y, ∃ (U : Y.affineOpens) (f : Γ(Y, U.1)), x ∈ U.1 ∧ F.ideal U = Ideal.span {f})
    (hnz : EmbeddedResolution.NonzeroOnComponents F) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor F := by
  intro x
  obtain ⟨U, f, hxU, hFU⟩ := hF x
  refine ⟨U, f, hxU, ?_, hFU⟩

  have hsupp : ∀ z (hz : z ∈ U.1), Y.presheaf.germ U.1 z hz f = 0 → z ∈ F.support := by
    intro z hz h0
    rw [EmbeddedResolution.mem_support_iff_stalkIdeal_ne_top,
      EmbeddedResolution.stalkIdeal_eq_map_germ F z U hz, hFU, Ideal.map_span, Set.image_singleton]
    intro htop
    have h1 : (Y.presheaf.germ U.1 z hz).hom f = 0 := h0
    rw [h1, Ideal.span_singleton_eq_top] at htop
    exact not_isUnit_zero htop
  have hgerm : ∀ y (hy : y ∈ U.1), Y.presheaf.germ U.1 y hy f ≠ 0 := by
    intro y hy h0
    obtain ⟨W, hyW, i1, i2, hW⟩ := TopCat.Presheaf.germ_eq Y.presheaf y hy hy f 0 (by rw [h0, map_zero])
    have hWs : ∀ z ∈ W, z ∈ F.support := by
      intro z hzW
      refine hsupp z (i1.le hzW) ?_
      rw [← Y.presheaf.germ_res_apply i1 z hzW f, hW, map_zero, map_zero]
    obtain ⟨C, hC, hyC⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible ({y} : Set Y)
      isIrreducible_singleton
    have hnC := hnz C hC
    obtain ⟨z, hzC, hz⟩ := Set.not_subset.mp hnC
    obtain ⟨w, hwC, hw1, hw2⟩ := hC.1.2 ((F.support : Set Y)ᶜ) (W : Set Y) F.support.2.isOpen_compl W.2
      ⟨z, hzC, hz⟩ ⟨y, hyC rfl, hyW⟩
    exact hw1 (hWs w hw2)
  have key : ∀ g : Γ(Y, U.1), f * g = 0 → g = 0 := by
    intro g hg
    apply TopCat.Presheaf.section_ext Y.sheaf U.1 g 0
    intro y hy
    have := EmbeddedResolution.isDomain_stalk_of_smooth q y
    have h2 : Y.presheaf.germ U.1 y hy f * Y.presheaf.germ U.1 y hy g = 0 := by
      rw [← map_mul, hg, map_zero]
    rw [map_zero]
    exact (mul_eq_zero.mp h2).resolve_left (hgerm y hy)
  rw [mem_nonZeroDivisors_iff]
  exact ⟨key, fun g hg => key g (by rw [mul_comm]; exact hg)⟩

/- English proof (translation)
Establish `hnzJ : EmbeddedResolution.NonzeroOnComponents J`. Rewrite using `[EmbeddedResolution.nonzeroOnComponents_iff]`. Conclude with `EmbeddedResolution.effectiveCartierSupportContainsNoComponent X J hJ`. Establish `hnz : EmbeddedResolution.NonzeroOnComponents (J.comap π)` using `EmbeddedResolution.nonzeroOnComponents_of_pow_mul_eq_comap EmbeddedResolution.effectiveCartierSupportContainsNoComponent π Z hπ 0 J (J.comap π) (by simp) hnzJ`. Conclude with `isLocallyGeneratedByNonZeroDivisor_of_span_singleton q (exists_span_singleton_comap π hJ) hnz`.
-/
theorem isLocallyGeneratedByNonZeroDivisor_comap_blowup {k : Type} [Field k] {X X' : Scheme.{0}} {π : X' ⟶ X}
    {Z : X.IdealSheafData} (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (q : X' ⟶ Spec (CommRingCat.of k)) [Smooth q]
    {J : X.IdealSheafData} (hJ : Blowup.IsLocallyGeneratedByNonZeroDivisor J) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor (J.comap π) := by
  have hnzJ : EmbeddedResolution.NonzeroOnComponents J := by
    rw [EmbeddedResolution.nonzeroOnComponents_iff]
    exact EmbeddedResolution.effectiveCartierSupportContainsNoComponent X J hJ
  have hnz : EmbeddedResolution.NonzeroOnComponents (J.comap π) :=
    EmbeddedResolution.nonzeroOnComponents_of_pow_mul_eq_comap
      EmbeddedResolution.effectiveCartierSupportContainsNoComponent π Z hπ 0 J (J.comap π) (by simp) hnzJ
  exact isLocallyGeneratedByNonZeroDivisor_of_span_singleton q (exists_span_singleton_comap π hJ) hnz

/- English proof (translation)
The claim follows from `| 0, _ => by simpa [BlowupSequence.exceptionalProduct] using Blowup.isLocallyGeneratedByNonZeroDivisor_top (s.obj 0) | i + 1, hi => by obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsm, -⟩ := id h have hlt : i < s.length := hi have hb : Blowup.IsBlowupAlongIdealSheaf (s.blowupMap i) ( …`.
-/
theorem isLocallyGeneratedByNonZeroDivisor_exceptionalProduct_le {k : Type} [Field k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {L : List X.IdealSheafData} {s : BlowupSequence X}
    (h : IsPrincipalizingSequence p I L s) :
    ∀ i, i ≤ s.length → Blowup.IsLocallyGeneratedByNonZeroDivisor (s.exceptionalProduct i)
  | 0, _ => by
    simpa [BlowupSequence.exceptionalProduct] using Blowup.isLocallyGeneratedByNonZeroDivisor_top (s.obj 0)
  | i + 1, hi => by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hsm, -⟩ := id h
    have hlt : i < s.length := hi
    have hb : Blowup.IsBlowupAlongIdealSheaf (s.blowupMap i) (s.center i) := s.isBlowup i hlt
    have ih := isLocallyGeneratedByNonZeroDivisor_exceptionalProduct_le h i hlt.le
    have : Smooth (s.structMap (i + 1) ≫ p) := hsm (i + 1) hi
    show Blowup.IsLocallyGeneratedByNonZeroDivisor
      ((s.exceptionalProduct i).comap (s.blowupMap i) * (s.center i).comap (s.blowupMap i))
    exact isLocallyGeneratedByNonZeroDivisor_mul
      (isLocallyGeneratedByNonZeroDivisor_comap_blowup hb (s.structMap (i + 1) ≫ p) ih)
      (Blowup.IsBlowupAlongIdealSheaf.isLocallyGeneratedByNonZeroDivisor_comap hb)

/- English proof (translation)
The claim follows from `isLocallyGeneratedByNonZeroDivisor_exceptionalProduct_le h s.length le_rfl`.
-/
theorem isLocallyGeneratedByNonZeroDivisor_exceptionalProduct {k : Type} [Field k] {X : Scheme.{0}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {L : List X.IdealSheafData} {s : BlowupSequence X}
    (h : IsPrincipalizingSequence p I L s) :
    Blowup.IsLocallyGeneratedByNonZeroDivisor (s.exceptionalProduct s.length) :=
  isLocallyGeneratedByNonZeroDivisor_exceptionalProduct_le h s.length le_rfl

/- English proof (translation)
Introduce `k _ _ X p _ _ _ I L s hI hL hs`. Take `⟨-, -, -, -, -, -, -, -, -, -, htop, -, -⟩` from `id hs`. Rewrite using `[htop]`. Conclude with `effCartier_of (isLocallyGeneratedByNonZeroDivisor_exceptionalProduct hs)`.
-/
theorem gEff : GEff := by
  intro k _ _ X p _ _ _ I L s hI hL hs
  obtain ⟨-, -, -, -, -, -, -, -, -, -, htop, -, -⟩ := id hs
  rw [htop]
  exact effCartier_of (isLocallyGeneratedByNonZeroDivisor_exceptionalProduct hs)

end PositivityTheory.ResPlug.GEndGen
