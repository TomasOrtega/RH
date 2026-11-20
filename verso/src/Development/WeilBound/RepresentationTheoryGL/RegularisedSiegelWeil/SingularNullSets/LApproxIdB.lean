import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Kdata
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LApproxIdC
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOneStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsStandardLocalMeasuresStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef (testT boxA fouA intF)

/- English proof (translation)
Introduce `F _ _ hF ψ hψ S ε hε ν hν`. Use `haveI : BorelSpace (AF F) := ⟨rfl⟩`. Take `⟨db, hdb⟩` from `GlobalTheory.T.exists_adelic_haar_covolume_one F`. Take `⟨⟨laminf, hinf⟩, hlamex⟩` from `GlobalTheory.T.exists_standard_local_measures F`. Use `choose lam hlam using hlamex`.

Take `⟨S₁, hS₁⟩` from `GlobalTheory.T.exists_local_approximate_identity F hF ψ hψ db hdb laminf lam hinf hlam`. Take `⟨ρ, U, hρ, hρt, hU, hUt, hinv, hint, -, hlim⟩` from `hS₁ (S ∪ S₁) Finset.subset_union_right`. Use `haveI : db.IsAddHaarMeasure := hdb.1`. Establish `hεε` using `idF_mul hε`. Establish `hp : Continuous (AddMonoidHom.mulLeft ε)` using `continuous_mul_left ε`.

Establish `hpp : ∀ x, AddMonoidHom.mulLeft ε (AddMonoidHom.mulLeft ε x) = AddMonoidHom.mulLeft ε x` using `fun x => by`. Simplify using `only [AddMonoidHom.coe_mulLeft, ← mul_assoc, hεε]`. Establish `hcY : IsClosed (((AddMonoidHom.mulLeft ε).ker : Set (AF F)))` using `isClosed_eq hp continuous_const`. Use `haveI : LocallyCompactSpace (AddMonoidHom.mulLeft ε).ker := hcY.locallyCompactSpace`. Use `haveI : LocallyCompactSpace (fixE ε) := (isClosed_eq hp continuous_id).locallyCompactSpace`.

Use `haveI := hν`. Use `haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SecondCountableTopology (AddMonoidHom.mulLeft ε).ker := TopologicalSpace.Subtype.secondCountableTopology _`. Use `haveI : SigmaCompactSpace (fixE ε) := inferInstance`. Use `haveI : SigmaCompactSpace (AddMonoidHom.mulLeft ε).ker := inferInstance`.

Use `haveI : SigmaFinite ν := inferInstance`. Take `⟨c, hc, hdec⟩` from `decomp (AddMonoidHom.mulLeft ε) hp hpp db ν (Measure.addHaar)`. Establish `hloc` using `fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), IsTopologicalRing (Fv F v) := fun v => (hloc v).1`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩`.

Use `haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1`. Establish `hne : ∀ k, ∫ y, testT (ρ k) (S ∪ S₁) (U k) y ∂db ≠ 0`. Introduce `k`. Rewrite using `[hint k]`. Use `mul_ne_zero (by exact_mod_cast (hρ k).2.2.2.ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)` and prove the remaining obligations.

Establish `h1 : 0 < (lam v) (U k v)` using `(hU k v).2.1.measure_pos (lam v) ⟨0, (hU k v).2.2⟩`. Establish `h2 : (lam v) (U k v) ≠ ⊤` using `(hU k v).1.measure_lt_top.ne`. Conclude with `(ENNReal.toReal_pos h1.ne' h2).ne'` after adjusting the coercions. Use `choose g Gc hGc hgI hgb hgint hgeq using fun k => kdata ψ hψ Finset.subset_union_left hε db ν Measure.addHaar c hc hdec (ρ k) (hρ k).1 (hρ k).2.1 (hρ k).2.2.1 (U k) (fun v => (hU k v).2.2) (hinv k).1 (hinv k).2 (hne k)`. Use `⟨g, fun k s => Gc k * tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)), fun k => {a | ε * a = a ∧ fstA F a ∈ tsupport (ρ k) ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v}, fun k => ⟨hgI k, hgb k, fun s => ⟨mul_nonneg (hGc k) (tR_nonneg (hρ k).2.2.1 _ _ _), hgint k s⟩⟩, fun h => ?_, fun k s hs => ?_, top1 S …` and prove the remaining obligations.

Establish `hl` using `hlim h.1`. Establish `hm : sndA F h.1 ∈ intF (S ∪ S₁)` using `fun v hv => by`. Rewrite using `[snd_eq, fix_snd hε (memH h) (fun h' => hv (Finset.mem_union_left _ h'))]`. Conclude with `zero_mem _`. Rewrite `hl` using `[Set.indicator_of_mem hm]`.

Simplify using `only [hgeq]`. Conclude with `hl`. Establish `ht : tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)) ≠ 0` using `fun h0 => hs (by simp only [h0, mul_zero])`. Unfold `tR at ht`. Establish `hρne : ρ k (fstA F (-(ε * s))) ≠ 0` using `fun h0 => ht (by rw [h0, zero_mul])`.

Establish `hbox : sndA F (-(ε * s)) ∈ boxA (S ∪ S₁) (U k)`. Assume the negation of the conclusion as `hn`. Conclude with `ht (by rw [Set.indicator_of_notMem hn, mul_zero])`. Conclude with `⟨by rw [mul_neg, ← mul_assoc, hεε], subset_tsupport _ hρne, fun v hv => hbox.1 v (Finset.mem_union_left _ hv)⟩`.
-/
theorem oneD : OneD := by
  intro F _ _ hF ψ hψ S ε hε ν hν
  classical
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨db, hdb⟩ := GlobalTheory.T.exists_adelic_haar_covolume_one F
  obtain ⟨⟨laminf, hinf⟩, hlamex⟩ := GlobalTheory.T.exists_standard_local_measures F
  choose lam hlam using hlamex
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.T.exists_local_approximate_identity F hF ψ hψ db hdb laminf lam hinf hlam
  obtain ⟨ρ, U, hρ, hρt, hU, hUt, hinv, hint, -, hlim⟩ := hS₁ (S ∪ S₁) Finset.subset_union_right
  haveI : db.IsAddHaarMeasure := hdb.1
  have hεε := idF_mul hε
  have hp : Continuous (AddMonoidHom.mulLeft ε) := continuous_mul_left ε
  have hpp : ∀ x, AddMonoidHom.mulLeft ε (AddMonoidHom.mulLeft ε x) = AddMonoidHom.mulLeft ε x := fun x => by
    simp only [AddMonoidHom.coe_mulLeft, ← mul_assoc, hεε]
  have hcY : IsClosed (((AddMonoidHom.mulLeft ε).ker : Set (AF F))) := isClosed_eq hp continuous_const
  haveI : LocallyCompactSpace (AddMonoidHom.mulLeft ε).ker := hcY.locallyCompactSpace
  haveI : LocallyCompactSpace (fixE ε) := (isClosed_eq hp continuous_id).locallyCompactSpace
  haveI := hν
  haveI : SecondCountableTopology (fixE ε) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (AddMonoidHom.mulLeft ε).ker := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace (fixE ε) := inferInstance
  haveI : SigmaCompactSpace (AddMonoidHom.mulLeft ε).ker := inferInstance
  haveI : SigmaFinite ν := inferInstance
  obtain ⟨c, hc, hdec⟩ := decomp (AddMonoidHom.mulLeft ε) hp hpp db ν (Measure.addHaar)
  have hloc := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  have hne : ∀ k, ∫ y, testT (ρ k) (S ∪ S₁) (U k) y ∂db ≠ 0 := by
    intro k
    rw [hint k]
    refine mul_ne_zero (by exact_mod_cast (hρ k).2.2.2.ne') (Finset.prod_ne_zero_iff.2 fun v _ => ?_)
    have h1 : 0 < (lam v) (U k v) := (hU k v).2.1.measure_pos (lam v) ⟨0, (hU k v).2.2⟩
    have h2 : (lam v) (U k v) ≠ ⊤ := (hU k v).1.measure_lt_top.ne
    exact_mod_cast (ENNReal.toReal_pos h1.ne' h2).ne'
  choose g Gc hGc hgI hgb hgint hgeq using fun k => kdata ψ hψ Finset.subset_union_left hε db ν Measure.addHaar c hc
    hdec (ρ k) (hρ k).1 (hρ k).2.1 (hρ k).2.2.1 (U k) (fun v => (hU k v).2.2) (hinv k).1 (hinv k).2 (hne k)
  refine ⟨g, fun k s => Gc k * tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)),
    fun k => {a | ε * a = a ∧ fstA F a ∈ tsupport (ρ k) ∧ ∀ v ∈ S, (sndA F a) v ∈ U k v},
    fun k => ⟨hgI k, hgb k, fun s => ⟨mul_nonneg (hGc k) (tR_nonneg (hρ k).2.2.1 _ _ _), hgint k s⟩⟩,
    fun h => ?_, fun k s hs => ?_, top1 S ε hε _ U hρt hUt⟩
  · have hl := hlim h.1
    have hm : sndA F h.1 ∈ intF (S ∪ S₁) := fun v hv => by
      rw [snd_eq, fix_snd hε (memH h) (fun h' => hv (Finset.mem_union_left _ h'))]
      exact zero_mem _
    rw [Set.indicator_of_mem hm] at hl
    simp only [hgeq]
    exact hl
  · have ht : tR (ρ k) (S ∪ S₁) (U k) (-(ε * s)) ≠ 0 := fun h0 => hs (by simp only [h0, mul_zero])
    unfold tR at ht
    have hρne : ρ k (fstA F (-(ε * s))) ≠ 0 := fun h0 => ht (by rw [h0, zero_mul])
    have hbox : sndA F (-(ε * s)) ∈ boxA (S ∪ S₁) (U k) := by
      by_contra hn
      exact ht (by rw [Set.indicator_of_notMem hn, mul_zero])
    exact ⟨by rw [mul_neg, ← mul_assoc, hεε], subset_tsupport _ hρne,
      fun v hv => hbox.1 v (Finset.mem_union_left _ hv)⟩

end PositivityTheory.Rg.Rsw.L.LApproxId

end
