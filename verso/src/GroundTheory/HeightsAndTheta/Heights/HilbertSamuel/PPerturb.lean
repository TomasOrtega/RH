import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨T, hT, rfl⟩` from `hP`. Use `⟨MvPolynomial.map φ '' T, ?_, by rw [Ideal.map_span]⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨f, hf, rfl⟩`. Take `⟨a, ha⟩` from `hT f hf`. Conclude with `⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset φ f hm) k⟩`.
-/
theorem isMultiHomogIdeal_map_coeff {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    {P : Ideal (MRingOver R ι)} (hP : IsMultiHomogIdeal P) :
    IsMultiHomogIdeal (P.map (MvPolynomial.map φ : MRingOver R ι →+* MRingOver S ι)) := by
  obtain ⟨T, hT, rfl⟩ := hP
  refine ⟨MvPolynomial.map φ '' T, ?_, by rw [Ideal.map_span]⟩
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hT f hf
  exact ⟨a, fun m hm k => ha m (MvPolynomial.support_map_subset φ f hm) k⟩

/- English proof (translation)
Use function extensionality and compare the values at `k`. Simplify using `[HermLine.zcomb, fsH, HermLine.ofMetrics]`.
-/
theorem zcomb_fsH_a [Fintype K] (L : HermLine ι) (q p : ℕ) :
    (HermLine.zcomb L (fsH ι) q p).a = (q : ℤ) • L.a + fun _ => (p : ℤ) := by
  funext k
  simp [HermLine.zcomb, fsH, HermLine.ofMetrics]

/- English proof (translation)
Introduce `K _ _ ι _ _ Ω _ _ y D L P0 p q _ hV _ hL hp hq`. Take `⟨n, w, hw, hgw, -⟩` from `hL.gen`. Establish `hhom : IsMultiHomogIdeal (mCoordIdeal y)` using `hV.2.1.2.1`. Establish `hfib` using `hFib K ι Ω y L.a n w hw hgw`. Use `⟨⟨hL.normalForm_baseLattice_le_dualSpan_sup_line, hSemi K ι P0 _ L p q hL.semipos, ?_, hGen K ι Ω y L p q hL.gen⟩, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[zcomb_fsH_a]`. Conclude with `hDeg K ι Ω y D L.a n w p q hV hw hgw hL.deg_pos hq`. Rewrite using `[zcomb_fsH_a]`. Conclude with `hAmp ℚ K ι (KH.genIdeal y) L.a p q (isMultiHomogIdeal_map_coeff _ hhom) hfib.1 hp`. Introduce `ℓ hℓ`.

Use `Fact.mk hℓ` as an intermediate fact. Rewrite using `[zcomb_fsH_a]`. Conclude with `hAmp (ZMod ℓ) K ι (fibreIdeal ℓ y) L.a p q (isMultiHomogIdeal_map_coeff _ hhom) (hfib.2 ℓ hℓ) hp`.
-/
theorem Perturb.proof (hGen : SmallGenTwist.Statement) (hSemi : SemiposTwist.Statement)
    (hDeg : GenDegTwist.Statement) (hFib : GenOnFibres.Statement) (hAmp : AmpleOfGenTwist.Statement) :
    Perturb.Statement := by
  intro K _ _ ι _ _ Ω _ _ y D L P0 p q _ hV _ hL hp hq
  obtain ⟨n, w, hw, hgw, -⟩ := hL.gen
  have hhom : IsMultiHomogIdeal (mCoordIdeal y) := hV.2.1.2.1
  have hfib := hFib K ι Ω y L.a n w hw hgw
  refine ⟨⟨hL.normalForm_baseLattice_le_dualSpan_sup_line, hSemi K ι P0 _ L p q hL.semipos, ?_, hGen K ι Ω y L p q hL.gen⟩, ?_, ?_⟩
  · rw [zcomb_fsH_a]
    exact hDeg K ι Ω y D L.a n w p q hV hw hgw hL.deg_pos hq
  · rw [zcomb_fsH_a]
    exact hAmp ℚ K ι (KH.genIdeal y) L.a p q (isMultiHomogIdeal_map_coeff _ hhom) hfib.1 hp
  · intro ℓ hℓ
    have := Fact.mk hℓ
    rw [zcomb_fsH_a]
    exact hAmp (ZMod ℓ) K ι (fibreIdeal ℓ y) L.a p q (isMultiHomogIdeal_map_coeff _ hhom) (hfib.2 ℓ hℓ) hp

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
