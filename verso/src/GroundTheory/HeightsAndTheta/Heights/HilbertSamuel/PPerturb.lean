import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPerturb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
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
Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules.
-/
theorem zcomb_fsH_a [Fintype K] (L : HermLine ι) (q p : ℕ) :
    (HermLine.zcomb L (fsH ι) q p).a = (q : ℤ) • L.a + fun _ => (p : ℤ) := by
  funext k
  simp [HermLine.zcomb, fsH, HermLine.ofMetrics]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
