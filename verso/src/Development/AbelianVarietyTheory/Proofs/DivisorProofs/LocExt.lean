import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSeparatedOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CInfAtSum
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

namespace GlobalTheory.ClosedExt

/- English proof (translation)
Use `GlobalTheory.LocExt.isSeparated_of_isProjOver hp` as an intermediate fact. Establish `hq : IsProjOver q`. Take `⟨N, i, hi, rfl⟩` from `hp`. Conclude with `⟨N, π ≫ i, inferInstance, by rw [Category.assoc, hπ]⟩`. Establish `hemb : IsClosedEmbedding (ptMap π hπ σ)`.

Use `CxPts.compactSpace σ hq` as an intermediate fact. Establish `hc : Continuous (ptMap π hπ σ)` using `continuous_of_comp (f := π) fun _ => rfl`. Use `hc.isClosedEmbedding fun y y' h => Subtype.ext ?_` and prove the remaining obligations. Conclude with `(cancel_mono π).1 (congrArg Subtype.val h)`. Distinguish the cases in `hx : ∃ y : CxPts q σ, ptMap π hπ σ y = x`.

Take `⟨y₀, rfl⟩` from `hx`. Take `⟨W, ι, _, g, F, O₀, h₁, h₂, h₃, h₄, h₅⟩` from `hu y₀`. Take `⟨t, ht, htW⟩` from `(π.isClosedEmbedding.isInducing.isOpen_iff).1 W.2`. Set `W₁ : X.Opens` to `⟨t, ht⟩`. Establish `hW₁ : π ⁻¹ᵁ W₁ = W` using `Opens.ext htW`.

Establish `hz₀ : π (y₀.1 (IsLocalRing.closedPoint ℂ)) ∈ W₁`. Use `mem_ptsIn.1 h₁` as an intermediate fact. Rewrite `this` using `[← hW₁]`. Conclude with `this`. Take `⟨W', hW'a, hzW', hW'le⟩` from `Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hz₀`.

Establish `hle : π ⁻¹ᵁ W' ≤ W`. Rewrite using `[← hW₁]`. Conclude with `fun a ha => hW'le ha`. Use `choose g' hg' using fun a => π.app_surjective W' hW'a (resG Y hle (g a))`. Establish `hval (y : CxPts q σ) (hy : y ∈ ptsIn q σ (π ⁻¹ᵁ W')) (a : ι) : ev p σ W' (g' a) (ptMap π hπ σ y) = ev q σ W (g a) y`.

Rewrite using `[← ev_res hle hy, ← hg' a]`. Conclude with `valR_comp y.1 π W' (g' a)`. Take `⟨s, hs, hsu⟩` from `h₅.exists_mem`. Take `⟨N, hNs, hN, hy₀N⟩` from `mem_nhds_iff.1 hs`. Take `⟨N', hN', hNN'⟩` from `(hemb.isInducing.isOpen_iff).1 hN`.

Establish `hE : IsOpen (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀)` using `(continuousOn_pi.2 fun a => continuousOn_ev (g' a)).isOpen_inter_preimage (isOpen_ptsIn W') h₂`. Establish `hy₀W' : y₀ ∈ ptsIn q σ (π ⁻¹ᵁ W')` using `mem_ptsIn.2 hzW'`. Use `⟨N' ∩ (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀), fun z => F fun a => ev p σ W' (g' a) z, hN'.inter hE, ⟨?_, ?_, ?_⟩, fun z hz => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Establish `: y₀ ∈ ptMap π hπ σ ⁻¹' N'` using `hNN'.symm ▸ hy₀N`. Conclude with `this`.

Conclude with `mem_ptsIn.2 hzW'`. Simplify using `only [Set.mem_preimage, hval y₀ hy₀W']`. Conclude with `h₃`. Conclude with `⟨W', ι, inferInstance, g', F, O₀, hz.2.1, h₂, hz.2.2, h₄, EventuallyEq.rfl⟩`. Establish `hyN : y ∈ N`.

Establish `: y ∈ ptMap π hπ σ ⁻¹' N'` using `hy.1`. Rewrite `this` using `[hNN']`. Then use the resulting hypothesis. Establish `hyW' : y ∈ ptsIn q σ (π ⁻¹ᵁ W')` using `mem_ptsIn.2 (mem_ptsIn.1 hy.2.1)`. Simplify using `only [hval y hyW']`. Conclude with `(hsu (hNs hyN)).symm`.

Conclude with `⟨(Set.range (ptMap π hπ σ))ᶜ, fun _ => 0, hemb.isClosed_range.isOpen_compl, hx, fun z _ => cInfAt_const 0 z, fun y hy => absurd (Set.mem_range_self y) hy⟩`.
-/
theorem locExt {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
    (hp : IsProjOver p) (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ)
    (hu : ∀ y, CInfAt u y) (x : CxPts p σ) :
    ∃ (O : Set (CxPts p σ)) (v : CxPts p σ → ℝ), IsOpen O ∧ x ∈ O ∧ (∀ z ∈ O, CInfAt v z) ∧
      ∀ y : CxPts q σ, ptMap π hπ σ y ∈ O → v (ptMap π hπ σ y) = u y := by
  have := GlobalTheory.LocExt.isSeparated_of_isProjOver hp
  have hq : IsProjOver q := by
    obtain ⟨N, i, hi, rfl⟩ := hp
    exact ⟨N, π ≫ i, inferInstance, by rw [Category.assoc, hπ]⟩
  have hemb : IsClosedEmbedding (ptMap π hπ σ) := by
    have := CxPts.compactSpace σ hq
    have hc : Continuous (ptMap π hπ σ) := continuous_of_comp (f := π) fun _ => rfl
    refine hc.isClosedEmbedding fun y y' h => Subtype.ext ?_
    exact (cancel_mono π).1 (congrArg Subtype.val h)
  by_cases hx : ∃ y : CxPts q σ, ptMap π hπ σ y = x
  · obtain ⟨y₀, rfl⟩ := hx
    obtain ⟨W, ι, _, g, F, O₀, h₁, h₂, h₃, h₄, h₅⟩ := hu y₀
    obtain ⟨t, ht, htW⟩ := (π.isClosedEmbedding.isInducing.isOpen_iff).1 W.2
    let W₁ : X.Opens := ⟨t, ht⟩
    have hW₁ : π ⁻¹ᵁ W₁ = W := Opens.ext htW
    have hz₀ : π (y₀.1 (IsLocalRing.closedPoint ℂ)) ∈ W₁ := by
      have := mem_ptsIn.1 h₁
      rw [← hW₁] at this
      exact this
    obtain ⟨W', hW'a, hzW', hW'le⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hz₀
    have hle : π ⁻¹ᵁ W' ≤ W := by
      rw [← hW₁]
      exact fun a ha => hW'le ha
    choose g' hg' using fun a => π.app_surjective W' hW'a (resG Y hle (g a))
    have hval (y : CxPts q σ) (hy : y ∈ ptsIn q σ (π ⁻¹ᵁ W')) (a : ι) :
        ev p σ W' (g' a) (ptMap π hπ σ y) = ev q σ W (g a) y := by
      rw [← ev_res hle hy, ← hg' a]
      exact valR_comp y.1 π W' (g' a)
    obtain ⟨s, hs, hsu⟩ := h₅.exists_mem
    obtain ⟨N, hNs, hN, hy₀N⟩ := mem_nhds_iff.1 hs
    obtain ⟨N', hN', hNN'⟩ := (hemb.isInducing.isOpen_iff).1 hN
    have hE : IsOpen (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀) :=
      (continuousOn_pi.2 fun a => continuousOn_ev (g' a)).isOpen_inter_preimage (isOpen_ptsIn W') h₂
    have hy₀W' : y₀ ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 hzW'
    refine ⟨N' ∩ (ptsIn p σ W' ∩ (fun z (a : ι) => ev p σ W' (g' a) z) ⁻¹' O₀),
      fun z => F fun a => ev p σ W' (g' a) z, hN'.inter hE, ⟨?_, ?_, ?_⟩, fun z hz => ?_, fun y hy => ?_⟩
    · have : y₀ ∈ ptMap π hπ σ ⁻¹' N' := hNN'.symm ▸ hy₀N
      exact this
    · exact mem_ptsIn.2 hzW'
    · simp only [Set.mem_preimage, hval y₀ hy₀W']
      exact h₃
    · exact ⟨W', ι, inferInstance, g', F, O₀, hz.2.1, h₂, hz.2.2, h₄, EventuallyEq.rfl⟩
    · have hyN : y ∈ N := by
        have : y ∈ ptMap π hπ σ ⁻¹' N' := hy.1
        rwa [hNN'] at this
      have hyW' : y ∈ ptsIn q σ (π ⁻¹ᵁ W') := mem_ptsIn.2 (mem_ptsIn.1 hy.2.1)
      simp only [hval y hyW']
      exact (hsu (hNs hyN)).symm
  · exact ⟨(Set.range (ptMap π hπ σ))ᶜ, fun _ => 0, hemb.isClosed_range.isOpen_compl, hx,
      fun z _ => cInfAt_const 0 z, fun y hy => absurd (Set.mem_range_self y) hy⟩

/- English proof (translation)
Introduce `k _ X Y p q σ hp π _ hπ u hu`. Conclude with `GlobalTheory.CInfGlue.glue k X p hp σ (CxPts q σ) (ptMap π hπ σ) u (locExt hp π hπ u hu)`.
-/
theorem exists_extension : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (u : CxPts q σ → ℝ), (∀ y, CInfAt u y) → ∃ v : CxPts p σ → ℝ, (∀ y, CInfAt v y) ∧ ∀ y, v (ptMap π hπ σ y) = u y := by
  intro k _ X Y p q σ hp π _ hπ u hu
  exact GlobalTheory.CInfGlue.glue k X p hp σ (CxPts q σ) (ptMap π hπ σ) u (locExt hp π hπ u hu)

end GlobalTheory.ClosedExt
