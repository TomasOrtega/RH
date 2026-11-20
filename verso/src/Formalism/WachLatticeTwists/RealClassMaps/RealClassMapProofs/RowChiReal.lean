import Formalism.WachLatticeTwists.RealClassMaps.Statement
import Formalism.WachLatticeTwists.ShapeRowIsomorphisms.Imports
import Formalism.WachLatticeTwists.CupProductVanishing.Imports

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR Formalism.RepresentationBoundsCohomology.JT Formalism.RepresentationBoundsCohomology.LocallyConstantCohomology Formalism.RepresentationBoundsCohomology.T2
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc IsCycOn IsFGTop cupFG RealLatG fracBilinear)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.FIN

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `p _ O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ek Ω _ _ _ _ _ Aw hp A T' _ _ _ _ _ _ _ M _ _ _ _ r χ E ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ D u hu v familyMassRatio iS1 familyMassSecondLine iS2 HfV HfV' Fs Im hO hF hA hcyc hε hD hπ hv hγ hBK hFs hRow hk`. Take `⟨K, hK, i, h1, -, -⟩` from `ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv (F := Ek) Aw hp`. Establish `hεD : D.ε = ε.comp (Aw.decompositionSubgroup Ek).subtype`. Use extensionality with `g`. Simplify using `[hε g]`.

Establish `hcD : IsCyc p K (ReciprocityTheory.ChartRestriction.T2.carry i D.ε)` using `h1 O D.ε (hεD ▸ hcyc)`. Take `⟨inv, invF, hc⟩` from `ReciprocityTheory.ChartRestriction.T2.exists_invariants_iso hK hO hF i hcD`. Establish `hD' : RealLatG i (withInv D inv.toLinearMap invF.toLinearMap)` using `⟨hcD, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩`. Set `j1 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT)` to `familyMassRatio`. Establish `j2 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT)` using `iS1`.

Set `j3 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT')` to `familyMassSecondLine`. Establish `j4 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT')` using `iS2`. Establish `hBK' : ∀ a, a ∈ HfV ↔ ∀ b ∈ HfV', fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap)) a b = 0`. Introduce `a`. Rewrite using `[hBK a]`.

Use `forall₂_congr fun b _ => ?_` and prove the remaining obligations. Use `show _ ↔ invF (cupFG D a b) = 0`. Rewrite using `[LinearEquiv.map_eq_zero_iff]`. Take `⟨_, hbk⟩` from `bkInRow p K O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek) (withInv D inv.toLinearMap invF.toLinearMap) i u hu HfV HfV' hK hO hF hD' inv.injective invF.injective hc hBK'`. Take `⟨C₁, c1, c2, c3, c3', c6, c7⟩` from `hRow`.

Set `pairD` to `fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap))`. Use `⟨prK (withInv D inv.toLinearMap invF.toLinearMap) _ hk, pairD, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hFs]`. Conclude with `hbk`. Use `⟨C₁, fun z => Continuous fun q : _ × _ => z q.1 q.2, fun f => Continuous f, fun f => Continuous f, fun f => Continuous f, c1, c2, c3, ?_, ?_, c6, c7⟩` and prove the remaining obligations.

Conclude with `clause4GK p K O A T' _ r χ E (Aw.decompositionSubgroup Ek) ε hK hO i (hεD ▸ hcD) hA`. Conclude with `clause5Row O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek) ε T₁ T₂ ρ₁ ρ₂ π γ (withInv D inv.toLinearMap invF.toLinearMap) u hu v hε hD.contT hπ hv hγ hk C₁ c3'`.
-/
theorem rowRhoReal : StatRowRhoReal := by
  intro p _ O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ek Ω _ _ _ _ _ Aw hp A T' _ _ _ _ _ _ _
    M _ _ _ _ r χ E ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ D u hu v familyMassRatio iS1 familyMassSecondLine iS2 HfV HfV' Fs Im hO hF hA hcyc hε hD hπ
    hv hγ hBK hFs hRow hk
  obtain ⟨K, hK, i, h1, -, -⟩ := ReciprocityTheory.ChartRestriction.T2.exists_dec_equiv (F := Ek) Aw hp
  have hεD : D.ε = ε.comp (Aw.decompositionSubgroup Ek).subtype := by
    ext g; simp [hε g]
  have hcD : IsCyc p K (ReciprocityTheory.ChartRestriction.T2.carry i D.ε) := h1 O D.ε (hεD ▸ hcyc)
  obtain ⟨inv, invF, hc⟩ := ReciprocityTheory.ChartRestriction.T2.exists_invariants_iso hK hO hF i hcD
  have hD' : RealLatG i (withInv D inv.toLinearMap invF.toLinearMap) :=
    ⟨hcD, hD.lat, hD.perf, hD.contT, hD.openT, hD.t2, hD.t2', hD.cs, hD.cs'⟩
  let j1 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := familyMassRatio
  have j2 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT) := iS1
  let j3 : Module (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := familyMassSecondLine
  have j4 : IsScalarTower O (FractionRing O) (H1 (withInv D inv.toLinearMap invF.toLinearMap).ρT') := iS2
  have hBK' : ∀ a, a ∈ HfV ↔ ∀ b ∈ HfV',
      fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap)) a b = 0 := by
    intro a
    rw [hBK a]
    refine forall₂_congr fun b _ => ?_
    show _ ↔ invF (cupFG D a b) = 0
    rw [LinearEquiv.map_eq_zero_iff]
  obtain ⟨_, hbk⟩ := bkInRow p K O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek)
    (withInv D inv.toLinearMap invF.toLinearMap) i u hu HfV HfV' hK hO hF hD' inv.injective invF.injective hc hBK'
  obtain ⟨C₁, c1, c2, c3, c3', c6, c7⟩ := hRow
  let pairD := fracBilinear (pairF (withInv D inv.toLinearMap invF.toLinearMap))
  refine ⟨prK (withInv D inv.toLinearMap invF.toLinearMap) _ hk, pairD, ?_, ?_⟩
  · rw [hFs]; exact hbk
  · refine ⟨C₁, fun z => Continuous fun q : _ × _ => z q.1 q.2, fun f => Continuous f, fun f => Continuous f,
      fun f => Continuous f, c1, c2, c3, ?_, ?_, c6, c7⟩
    · exact clause4GK p K O A T' _ r χ E (Aw.decompositionSubgroup Ek) ε hK hO i (hεD ▸ hcD) hA
    · exact clause5Row O VT VT' A T' _ M r χ (Aw.decompositionSubgroup Ek) ε T₁ T₂ ρ₁ ρ₂ π γ
        (withInv D inv.toLinearMap invF.toLinearMap) u hu v hε hD.contT hπ hv hγ hk C₁ c3'

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `p _ O _ _ _ _ _ hinj Ek Ω _ _ _ _ _ Aw hp pl hpl A T' _ _ _ _ M _ _ _ _ r χ E ε e hcyc hM hact F hF1 hF0 uu ww s m d U hTB`. Take `⟨sh1, sh0⟩` from `shapeDec p O hinj Ek Ω Aw hp pl hpl A T' M r χ ε e hcyc hM hact`. Use `⟨?_, hTB, ?_⟩` and prove the remaining obligations. Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases. Rewrite using `[hF0 he]`.

Conclude with `inf_le_left`. Rewrite using `[hF1 he]`. Conclude with `bot_le`. Break down `Nat.eq_zero_or_pos e with he | he` into its components or cases. Use `sh0 he` as an intermediate fact.

Rewrite using `[hF0 he]`. Unfold `QuotShape at this ⊢`. Rewrite using `[Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]` and apply the resulting hypothesis. Rewrite using `[hF1 he]`. Conclude with `sh1 he`.
-/
theorem rowChiReal : StatRowChiReal := by
  intro p _ O _ _ _ _ _ hinj Ek Ω _ _ _ _ _ Aw hp pl hpl A T' _ _ _ _ M _ _ _ _ r χ E ε e hcyc hM hact F hF1 hF0
    uu ww s m d U hTB
  obtain ⟨sh1, sh0⟩ := shapeDec p O hinj Ek Ω Aw hp pl hpl A T' M r χ ε e hcyc hM hact
  refine ⟨?_, hTB, ?_⟩
  · rcases Nat.eq_zero_or_pos e with he | he
    · rw [hF0 he]; exact inf_le_left
    · rw [hF1 he]; exact bot_le
  · rcases Nat.eq_zero_or_pos e with he | he
    · have := sh0 he
      rw [hF0 he]
      unfold QuotShape at this ⊢
      rwa [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
    · rw [hF1 he]; exact sh1 he

end Formalism.RepresentationBoundsCohomology.FIN
