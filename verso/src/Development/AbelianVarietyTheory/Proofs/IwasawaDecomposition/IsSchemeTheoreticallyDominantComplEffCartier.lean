import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratesAlong
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

namespace GlobalTheory.ProjBlowup

/- English proof (translation)
Introduce `W I hI`. Use `choose U f hxU hf hIU using hI`. Use `⟨le_bot_iff.1 (Scheme.IdealSheafData.le_of_iSup_eq_top U ?_ fun x s hs => ?_)⟩` and prove the remaining obligations. Conclude with `top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩`. Establish `h0` using `Scheme.Hom.ideal_ker_le _ (U x) hs`.

Rewrite `h0` using `[RingHom.mem_ker, Scheme.Opens.ι_app]`. Establish `hle : W.basicOpen (f x) ≤ (Scheme.Opens.ι (X` using `W) I.support.compl) ''ᵁ ((Scheme.Opens.ι (X := W) I.support.compl) ⁻¹ᵁ (U x).1) := by`. Introduce `y hy`. Establish `hyU : y ∈ (U x).1` using `W.basicOpen_le (f x) hy`. Establish `hyc : y ∈ I.support.compl`.

Introduce `hy'`. Use `(Scheme.IdealSheafData.mem_support_iff_of_mem hyU).1 hy'` as an intermediate fact. Rewrite `this` using `[Scheme.mem_zeroLocus_iff]`. Conclude with `this (f x) (by rw [hIU]; exact Ideal.subset_span rfl) hy`. Conclude with `⟨⟨y, hyc⟩, hyU, rfl⟩`.

Use `(U x).2.isLocalization_basicOpen (f x)` as an intermediate fact. Establish `hinj` using `IsLocalization.injective (M := Submonoid.powers (f x)) Γ(W, W.basicOpen (f x)) ((Submonoid.powers_le).2 (hf x))`. Establish `h1 : algebraMap Γ(W, (U x).1) Γ(W, W.basicOpen (f x)) s = 0`. Establish `h2` using `congrArg (W.presheaf.map (homOfLE hle).op).hom h0`. Establish `h3` using `h2.trans (map_zero (W.presheaf.map (homOfLE hle).op).hom)`.

Use `Eq.trans ?_ h3` and prove the remaining obligations. Use `erw [← CommRingCat.comp_apply, ← Functor.map_comp]`. Both sides reduce to the same expression. Establish `: s = 0` using `hinj (by rw [h1, map_zero])`. Simplify using `[this]`.
-/
theorem isSchemeTheoreticallyDominant_compl_of_effCartier :
    ∀ (W : Scheme.{0}) (I : W.IdealSheafData), FinalTheorems.EffCartier I →
      IsSchemeTheoreticallyDominant (Scheme.Opens.ι (X := W) I.support.compl) := by
  intro W I hI
  choose U f hxU hf hIU using hI
  refine ⟨le_bot_iff.1 (Scheme.IdealSheafData.le_of_iSup_eq_top U ?_ fun x s hs => ?_)⟩
  · exact top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hxU x⟩
  · have h0 := Scheme.Hom.ideal_ker_le _ (U x) hs
    rw [RingHom.mem_ker, Scheme.Opens.ι_app] at h0
    have hle : W.basicOpen (f x) ≤ (Scheme.Opens.ι (X := W) I.support.compl) ''ᵁ
        ((Scheme.Opens.ι (X := W) I.support.compl) ⁻¹ᵁ (U x).1) := by
      intro y hy
      have hyU : y ∈ (U x).1 := W.basicOpen_le (f x) hy
      have hyc : y ∈ I.support.compl := by
        intro hy'
        have := (Scheme.IdealSheafData.mem_support_iff_of_mem hyU).1 hy'
        rw [Scheme.mem_zeroLocus_iff] at this
        exact this (f x) (by rw [hIU]; exact Ideal.subset_span rfl) hy
      exact ⟨⟨y, hyc⟩, hyU, rfl⟩
    have := (U x).2.isLocalization_basicOpen (f x)
    have hinj := IsLocalization.injective (M := Submonoid.powers (f x)) Γ(W, W.basicOpen (f x))
      ((Submonoid.powers_le).2 (hf x))
    have h1 : algebraMap Γ(W, (U x).1) Γ(W, W.basicOpen (f x)) s = 0 := by
      have h2 := congrArg (W.presheaf.map (homOfLE hle).op).hom h0
      have h3 := h2.trans (map_zero (W.presheaf.map (homOfLE hle).op).hom)
      refine Eq.trans ?_ h3
      erw [← CommRingCat.comp_apply, ← Functor.map_comp]
      rfl
    have : s = 0 := hinj (by rw [h1, map_zero])
    simp [this]

end GlobalTheory.ProjBlowup
