import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanInputNefAmpleSectionCountStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.KleimanGenericPointSectionInputStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.AmpleSt
import Development.WeilBound.CoreStatements.HodgeTatePoints.A12
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PAmpleOfGenTwist
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenTwistVanish
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenKoszulStep
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKoszulCechComplex
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKoszulCechExact
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PKleimanScheme
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PGeneratedCechTieX
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.KleimanNefF
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSegreBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.RelDimMIdealOverEqTrdeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsMultiProjPrimeSegreLift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ExistsNeZeroOfWeight
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ZpowMemSubalgebraOfInvMem

namespace PositivityTheory.KAmp

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman2 (IsNef IsGenerated KAt baseDeg)
open GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization (segreJoin)

/- English proof (translation)
The claim follows from `(GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.1 d`.
-/
theorem kAt_all (d : ℕ) : KAt d := (GlobalTheory.T.kleiman_input_nef_ample_section_count GlobalTheory.T.kleiman_genericPointSectionInput).2.1 d

/- English proof (translation)
The claim follows from `HilbertSamuel.GenTwistVanish.proof PositivityTheory.HtPt.Ktw.a11 HilbertSamuel.QuotPartGraded.full (HilbertSamuel.GenKoszulStep.proof HilbertSamuel.KoszulCechComplex.proof HilbertSamuel.KoszulCechExact.proof HilbertSamuel.DoubleComplexVanish.full Kleiman.KHCechDSq.full Kleiman.KH …`.
-/
theorem genTwistVanish : HilbertSamuel.GenTwistVanish.Statement :=
  HilbertSamuel.GenTwistVanish.proof PositivityTheory.HtPt.Ktw.a11 HilbertSamuel.QuotPartGraded.full
    (HilbertSamuel.GenKoszulStep.proof HilbertSamuel.KoszulCechComplex.proof HilbertSamuel.KoszulCechExact.proof
      HilbertSamuel.DoubleComplexVanish.full Kleiman.KHCechDSq.full Kleiman.KHCechDDeg.full)

/- English proof (translation)
The claim follows from `HilbertSamuel.AmpleOfGenTwist.proof HilbertSamuel.GenTwistGenerated.full genTwistVanish`.
-/
theorem ampleOfGenTwist : HilbertSamuel.AmpleOfGenTwist.Statement :=
  HilbertSamuel.AmpleOfGenTwist.proof HilbertSamuel.GenTwistGenerated.full genTwistVanish

/- English proof (translation)
Introduce `c0 hc`. Take `⟨u, hu, hsum⟩` from `h (Kleiman.SectionsOverLocalization.segreChart c0 c0) (Kleiman.SectionsOverLocalization.segreChart_adm y (Kleiman.SectionsOverLocalization.segreVec_ne_zero y hc) hc)`. Use `⟨u, fun j => Kleiman.SectionsOverLocalization.segre_diag_le y c0 (hu j), ?_⟩` and prove the remaining obligations. Establish `e1 : ∀ k : K, segreJoin y ⟨Sum.inr k, Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inr k)⟩ = y ⟨k, c0 k⟩` using `fun _ => rfl`. Establish `e2 : segreJoin y ⟨Sum.inl (), Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl ())⟩ = ∏ k, y ⟨k, c0 k⟩` using `rfl`.

Use `set D : Unit ⊕ K → ℤ := IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ()) with hD`. Establish `e3 : ∀ k : K, D (Sum.inr k) = β k`. Introduce `k`. Simplify using `[hD, IndefiniteRowSideFullHecke.Kleiman2.pullDeg, baseDeg]`. Establish `e4 : D (Sum.inl ()) = c`.

Simplify using `[hD, IndefiniteRowSideFullHecke.Kleiman2.pullDeg, baseDeg]`. Establish `hprod : (∏ k, segreJoin y ⟨k, Kleiman.SectionsOverLocalization.segreChart c0 c0 k⟩ ^ (-D k)) = ∏ k, y ⟨k, c0 k⟩ ^ (-(β k + c))`. Rewrite using `[Fintype.prod_sum_type]`. Establish `hu1 : (∏ u : Unit, segreJoin y ⟨Sum.inl u, Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl u)⟩ ^ (-D (Sum.inl u))) = (∏ k, y ⟨k, c0 k⟩) ^ (-c)`. Rewrite using `[Fintype.prod_unique]`.

Use `show segreJoin y ⟨Sum.inl (), Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl ())⟩ ^ (-D (Sum.inl ())) = _`. Rewrite using `[e2, e4]`. Rewrite using `[hu1, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[e1, e3, ← zpow_add₀ (hc k)]`.

Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hsum` using `[hprod]`. Conclude with `hsum`.
-/
theorem generatesOver_segreJoin_twist {S : Type} [CommRing S] {K : Type} [Fintype K] [DecidableEq K]
    {ι : K → Type} {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (β : K → ℤ) (c : ℤ) {n : ℕ}
    (η : Fin n → Ω)
    (h : KH.GeneratesOver S (segreJoin y) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ())) η) :
    KH.GeneratesOver S y (β + fun _ => c) η := by
  intro c0 hc
  obtain ⟨u, hu, hsum⟩ := h (Kleiman.SectionsOverLocalization.segreChart c0 c0)
    (Kleiman.SectionsOverLocalization.segreChart_adm y (Kleiman.SectionsOverLocalization.segreVec_ne_zero y hc) hc)
  refine ⟨u, fun j => Kleiman.SectionsOverLocalization.segre_diag_le y c0 (hu j), ?_⟩
  have e1 : ∀ k : K, segreJoin y ⟨Sum.inr k, Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inr k)⟩ = y ⟨k, c0 k⟩ :=
    fun _ => rfl
  have e2 : segreJoin y ⟨Sum.inl (), Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl ())⟩ = ∏ k, y ⟨k, c0 k⟩ := rfl
  set D : Unit ⊕ K → ℤ := IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) β + c • baseDeg (Sum.inl ()) with hD
  have e3 : ∀ k : K, D (Sum.inr k) = β k := by
    intro k
    simp [hD, IndefiniteRowSideFullHecke.Kleiman2.pullDeg, baseDeg]
  have e4 : D (Sum.inl ()) = c := by
    simp [hD, IndefiniteRowSideFullHecke.Kleiman2.pullDeg, baseDeg]
  have hprod : (∏ k, segreJoin y ⟨k, Kleiman.SectionsOverLocalization.segreChart c0 c0 k⟩ ^ (-D k)) =
      ∏ k, y ⟨k, c0 k⟩ ^ (-(β k + c)) := by
    rw [Fintype.prod_sum_type]
    have hu1 : (∏ u : Unit, segreJoin y ⟨Sum.inl u, Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl u)⟩ ^
        (-D (Sum.inl u))) = (∏ k, y ⟨k, c0 k⟩) ^ (-c) := by
      rw [Fintype.prod_unique]
      show segreJoin y ⟨Sum.inl (), Kleiman.SectionsOverLocalization.segreChart c0 c0 (Sum.inl ())⟩ ^ (-D (Sum.inl ())) = _
      rw [e2, e4]
    rw [hu1, ← Finset.prod_zpow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [e1, e3, ← zpow_add₀ (hc k)]
    congr 1
    ring
  rw [hprod] at hsum
  exact hsum

/- English proof (translation)
Take `⟨a', m, ha', hm, hva⟩` from `kAt_all d F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ()) (Kleiman.SectionsOverLocalization.SegreBase.proof F K ι Ω y hnz).1 ((Kleiman.SectionsOverLocalization.SegreDim.proof F K ι Ω y hnz).trans hrel) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg α) ((Kleiman.SectionsOverLocalization …`. Take `⟨n, x', hx', hgen, -⟩` from `hva`. Establish `e : a' • IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁` using `Unit) α + m • baseDeg (Sum.inl ()) = IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (a' • α) + m • baseDeg (Sum.inl ()) := by`. Use `congr 1`. Use function extensionality and compare the values at `k`.

Apply the tactic sequence `cases k <;> simp [IndefiniteRowSideFullHecke.Kleiman2.pullDeg, Pi.mul_apply, Pi.natCast_apply]`. Rewrite `hx'`, `hgen` using `[e]`. Use `⟨a', m, ha', hm, n, x', fun j => ?_, generatesOver_segreJoin_twist y (a' • α) m x' hgen⟩` and prove the remaining obligations. Use `hx' j` as an intermediate fact. Rewrite `this` using `[Kleiman.SectionsOverLocalization.SegreTwist.proof F K ι Ω y hnz]`. Then use the resulting hypothesis.
-/
theorem generated_of_nef (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type)
    [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra F Ω] (y : (Σ k, ι k) → Ω) (d : ℕ) (α : K → ℤ)
    (hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (hrel : FieldNumbers.relDim (KH.mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)))
    (hnef : IsNef F y α) (t : ℚ) (ht : 0 < t) :
    ∃ (a' : ℕ) (m : ℤ), 1 ≤ a' ∧ (m : ℚ) = a' * t ∧ IsGenerated F y (a' • α + fun _ => m) := by
  obtain ⟨a', m, ha', hm, hva⟩ := kAt_all d F (Unit ⊕ K) _ Ω (segreJoin y) (Sum.inl ())
    (Kleiman.SectionsOverLocalization.SegreBase.proof F K ι Ω y hnz).1
    ((Kleiman.SectionsOverLocalization.SegreDim.proof F K ι Ω y hnz).trans hrel) (IndefiniteRowSideFullHecke.Kleiman2.pullDeg α)
    ((Kleiman.SectionsOverLocalization.SegreNef.proof Kleiman.SectionsOverLocalization.SegreDim.proof Kleiman.SectionsOverLocalization.SegreNum.proof
      F K ι Ω y hnz α).2 hnef) t ht
  obtain ⟨n, x', hx', hgen, -⟩ := hva
  have e : a' • IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) α + m • baseDeg (Sum.inl ()) =
      IndefiniteRowSideFullHecke.Kleiman2.pullDeg (K₁ := Unit) (a' • α) + m • baseDeg (Sum.inl ()) := by
    congr 1
    funext k
    cases k <;> simp [IndefiniteRowSideFullHecke.Kleiman2.pullDeg, Pi.mul_apply, Pi.natCast_apply]
  rw [e] at hx' hgen
  refine ⟨a', m, ha', hm, n, x', fun j => ?_, generatesOver_segreJoin_twist y (a' • α) m x' hgen⟩
  have := hx' j
  rwa [Kleiman.SectionsOverLocalization.SegreTwist.proof F K ι Ω y hnz] at this

/- English proof (translation)
Introduce `F _ K _ _ ι _ _ I V d α b a hI hV hnef hb ha`. Establish `: V.IsPrime` using `hV.1.1`. Establish `hVd` using `HilbertSamuel.KleimanNefF.isMultiProjPrime_dvr hV.1`. Use `set y := Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt (O := F) V`. Establish `hy : KH.mIdealOver F y = V` using `Kleiman.SectionsOverLocalization.ModelGenericPoint.mIdealOver_genPt V hVd.multiHomog`.

Establish `hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0` using `fun k => by`. Take `⟨i, hi⟩` from `hV.1.2.2 k`. Conclude with `⟨i, (Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt_ne_zero V _).2 hi⟩`. Establish `hrel : FieldNumbers.relDim (KH.mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ))`. Rewrite using `[hy]`.

Conclude with `(FieldNumbers.CutRegular.relDim_eq_natCast_iff V d).2 hV.2`. Establish `hnef' : IsNef F y α`. Introduce `W hW hle hW1`. Rewrite `hle` using `[hy]`. Establish `hWF : IsProjVarF W 1` using `⟨⟨hW.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2 hW.multiHomog, hW.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩`.

Establish `h` using `hnef W hWF hle`. Rewrite `h` using `[HilbertSamuel.KleimanNefF.eq_intNum hI 1 W _ hWF]`. Then use the resulting hypothesis. Establish `hb' : (0 : ℚ) < b` using `by exact_mod_cast hb`. Establish `ha₀ : (0 : ℚ) < a` using `by exact_mod_cast ha`. Take `⟨a', m, ha', hm, hgen⟩` from `generated_of_nef F K ι _ y d α hnz hrel hnef' ((a : ℚ) / (2 * b)) (by positivity)`.

Establish `hGV : KH.GeneratedV F V (a' • α + fun _ => m)`. Use `Kleiman.SectionsOverLocalization.GeneratedCechTie.proof F K ι _ y _ hnz hgen` as an intermediate fact. Rewrite `this` using `[hy]`. Then use the resulting hypothesis. Establish `hamp` using `ampleOfGenTwist F K ι V _ (a' * a) (2 * b) hV.1.2.1 hGV (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))`. Establish `hm' : (2 * (b : ℤ)) * m = a' * a`.

Establish `hq : (2 * (b : ℚ)) * m = a' * a`. Rewrite using `[hm]`. Clear the denominators using the available nonvanishing facts. Conclude with `hq` after adjusting the coercions. Establish `e : ((2 * b : ℕ) : ℤ) • (a' • α + fun _ => m) + (fun _ => ((a' * a : ℕ) : ℤ)) = (2 * a') • (b • α + fun _ => (a : ℤ))`.

Use function extensionality and compare the values at `k`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]`. Use `push_cast`. Take the linear combination `hm'`. Rewrite `hamp` using `[e]`.

Conclude with `HilbertSamuel.ampleV_of_nsmul (by omega) hamp`.
-/
theorem kAmp : KH.KAmpStatement := by
  intro F _ K _ _ ι _ _ I V d α b a hI hV hnef hb ha
  classical
  have : V.IsPrime := hV.1.1
  have hVd := HilbertSamuel.KleimanNefF.isMultiProjPrime_dvr hV.1
  set y := Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt (O := F) V
  have hy : KH.mIdealOver F y = V :=
    Kleiman.SectionsOverLocalization.ModelGenericPoint.mIdealOver_genPt V hVd.multiHomog
  have hnz : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := hV.1.2.2 k
    exact ⟨i, (Kleiman.SectionsOverLocalization.ModelGenericPoint.genPt_ne_zero V _).2 hi⟩
  have hrel : FieldNumbers.relDim (KH.mIdealOver F y) = ((d : ℕ) : WithBot (WithTop ℤ)) := by
    rw [hy]
    exact (FieldNumbers.CutRegular.relDim_eq_natCast_iff V d).2 hV.2
  have hnef' : IsNef F y α := by
    intro W hW hle hW1
    rw [hy] at hle
    have hWF : IsProjVarF W 1 :=
      ⟨⟨hW.isPrime, (NumbersDVR.VocabMultiHomogIdeal.proof NumbersDVR.VocabMultiHomog.proof F K ι W).2
        hW.multiHomog, hW.relevant⟩, (FieldNumbers.CutRegular.relDim_eq_natCast_iff W 1).1 hW1⟩
    have h := hnef W hWF hle
    rwa [HilbertSamuel.KleimanNefF.eq_intNum hI 1 W _ hWF] at h
  have hb' : (0 : ℚ) < b := by exact_mod_cast hb
  have ha₀ : (0 : ℚ) < a := by exact_mod_cast ha
  obtain ⟨a', m, ha', hm, hgen⟩ :=
    generated_of_nef F K ι _ y d α hnz hrel hnef' ((a : ℚ) / (2 * b)) (by positivity)
  have hGV : KH.GeneratedV F V (a' • α + fun _ => m) := by
    have := Kleiman.SectionsOverLocalization.GeneratedCechTie.proof F K ι _ y _ hnz hgen
    rwa [hy] at this
  have hamp := ampleOfGenTwist F K ι V _ (a' * a) (2 * b) hV.1.2.1 hGV
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))
  have hm' : (2 * (b : ℤ)) * m = a' * a := by
    have hq : (2 * (b : ℚ)) * m = a' * a := by
      rw [hm]
      field_simp
    exact_mod_cast hq
  have e : ((2 * b : ℕ) : ℤ) • (a' • α + fun _ => m) + (fun _ => ((a' * a : ℕ) : ℤ)) =
      (2 * a') • (b • α + fun _ => (a : ℤ)) := by
    funext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    push_cast
    linear_combination hm'
  rw [e] at hamp
  exact HilbertSamuel.ampleV_of_nsmul (by omega) hamp

end PositivityTheory.KAmp
