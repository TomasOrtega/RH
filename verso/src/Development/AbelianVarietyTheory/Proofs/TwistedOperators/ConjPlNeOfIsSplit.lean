import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UpNeNSOfUpNe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstMemberParameterInvOfChainParameterInvStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainTw.ParInv

variable {D : D7}

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Use `show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal`. Rewrite using `[← Ideal.comap_symm, Ideal.mem_comap]`. Establish `: (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x`.

Apply `RingOfIntegers.ext` to reduce the goal to its premises. Simplify using `[Formalism.DivisionValues.cO, Formalism.L2.Col.cO]`. Both sides reduce to the same expression. Rewrite using `[this]`.
-/
theorem conjP_eq_conjPl' (P : HeightOneSpectrum (𝓞 D.host.E)) : Formalism.L2.Col.conjPrime₂ P = Formalism.DivisionValues.conjPl P := by
  apply HeightOneSpectrum.ext
  ext x
  show Formalism.L2.Col.cO _ x ∈ P.asIdeal ↔ x ∈ Ideal.map (Formalism.DivisionValues.cO D.host.E) P.asIdeal
  rw [← Ideal.comap_symm, Ideal.mem_comap]
  have : (Formalism.DivisionValues.cO D.host.E).symm x = Formalism.L2.Col.cO _ x := by
    apply RingOfIntegers.ext
    simp [Formalism.DivisionValues.cO, Formalism.L2.Col.cO]
    rfl
  rw [this]

/- English proof (translation)
Rewrite using `[← conjP_eq_conjPl', GlobalTheory.GridPlaces.under_conjP]`.
-/
theorem under_conjPl (w : HeightOneSpectrum (𝓞 D.host.E)) :
    (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
  rw [← conjP_eq_conjPl', GlobalTheory.GridPlaces.under_conjP]

/- English proof (translation)
Rewrite using `[Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]`. Conclude with `(Nat.card_congr (Ideal.quotientEquiv P.asIdeal (Formalism.DivisionValues.conjPl P).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm`.
-/
theorem absNorm_conjPl' (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Ideal.absNorm (Formalism.DivisionValues.conjPl P).asIdeal = Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal (Formalism.DivisionValues.conjPl P).asIdeal (Formalism.DivisionValues.cO D.host.E) rfl).toEquiv).symm

/- English proof (translation)
Introduce and unpack `hc`. Take `⟨P, Q, hPQ, hP, hQ⟩` from `hv`. Establish `key : ∀ R : HeightOneSpectrum (𝓞 D.host.E), Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) R.asIdeal = (w.under (𝓞 D.host.F)).asIdeal → R = w`. Introduce `R hR`. Break down `GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := R) (HeightOneSpectrum.ext hR) with h | h` into its components or cases.

Conclude with `h`. Rewrite using `[h, conjP_eq_conjPl', hc]`. Conclude with `hPQ ((key P hP).trans (key Q hQ).symm)`.
-/
theorem conjPl_ne_of_isSplit (w : HeightOneSpectrum (𝓞 D.host.E))
    (hv : Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F))) : Formalism.DivisionValues.conjPl w ≠ w := by
  rintro hc
  obtain ⟨P, Q, hPQ, hP, hQ⟩ := hv
  have key : ∀ R : HeightOneSpectrum (𝓞 D.host.E),
      Ideal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) R.asIdeal = (w.under (𝓞 D.host.F)).asIdeal → R = w := by
    intro R hR
    rcases GlobalTheory.GridPlaces.eq_or_eq_conjP (P := w) (Q := R) (HeightOneSpectrum.ext hR) with h | h
    · exact h
    · rw [h, conjP_eq_conjPl', hc]
  exact hPQ ((key P hP).trans (key Q hQ).symm)

end GlobalTheory.ChainTw.ParInv

end

open GlobalTheory.ChainTw.ParInv in

/- English proof (translation)
Introduce `D c tw htw j hj s hs u B hu hB`. Take `⟨hr, -, hflat⟩` from `hs`. Establish `hsd : IsSelfDualC s.V s.Λ` using `hflat.selfDual`. Take `⟨hu0, hpar⟩` from `hu`. Choose the witnesses or unpack the hypotheses as in `⟨v0, hv0⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hu0 (Subtype.ext (LinearMap.ext fun v => by simpa using h v))`. Establish `hP` using `hpar v0 hv0`. Establish `hcm` using `GlobalTheory.AdelicU.isCMExt_host D`.

Establish `hJ` using `GlobalTheory.Doubling.isHermND_gram s.V`. Establish `key : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))), chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹)`. Introduce `w hw`. Establish `hv : w.under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))` using `hw`. Establish `hd` using `(GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) hJ.2 hsd.1).2 (fun y => hsd.2 y) (w.under (𝓞 D.host.F))`.

Establish `hx` using `hP (w.under (𝓞 D.host.F)) hv w rfl`. Distinguish the cases in `hc : Formalism.DivisionValues.conjPl w = w`. Rewrite using `[hc]`. Break down `hx with ⟨hs, -⟩ | ⟨hin, -⟩` into its components or cases. Conclude with `absurd hc (conjPl_ne_of_isSplit w hs)`.

Conclude with `(GlobalTheory.LFun.ConjPlace.map_inv_of_isParamVec hin (hP _ hv w rfl)).symm`. Establish `hx'` using `hP (w.under (𝓞 D.host.F)) hv (Formalism.DivisionValues.conjPl w) (under_conjPl w)`. Conclude with `GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd (Ne.symm hc) hx hx'`. Introduce `w hw`. Establish `hw' : Formalism.DivisionValues.conjPl w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))` using `by show (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))`.

Rewrite using `[under_conjPl]`. Conclude with `hw`. Establish `hB' : B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹)` using `GlobalTheory.T.firstMemberParameter_inv_of_chainParameter_inv D c htw.com j hj B w hw (key w hw)`. Establish `e : GlobalTheory.ChainNS.invFam B w = B (Formalism.DivisionValues.conjPl w)` using `hB'.symm`. Rewrite using `[e]`.

Establish `h2` using `hB (Formalism.DivisionValues.conjPl w) hw'`. Rewrite `h2` using `[absNorm_conjPl']`. Then use the resulting hypothesis.
-/
theorem GlobalTheory.ChainTw.invFam_bounded : ∀ D : D7, ForStageQ D fun c _ j s => ∀ (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E), IsPar u (chainPar c B j) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) → GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) (GlobalTheory.ChainNS.invFam B) D.R.r ((D.R.r : ℝ) / 2) := by
  intro D c tw htw j hj s hs u B hu hB
  classical
  obtain ⟨hr, -, hflat⟩ := hs
  have hsd : IsSelfDualC s.V s.Λ := hflat.selfDual
  obtain ⟨hu0, hpar⟩ := hu
  obtain ⟨v0, hv0⟩ : ∃ v, PiLocalization₂.val u v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hu0 (Subtype.ext (LinearMap.ext fun v => by simpa using h v))
  have hP := hpar v0 hv0
  have hcm := GlobalTheory.AdelicU.isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram s.V
  have key : ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      chainPar c B j (Formalism.DivisionValues.conjPl w) = (chainPar c B j w).map (·⁻¹) := by
    intro w hw
    have hv : w.under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := hw
    have hd :=
      (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) hJ.2 hsd.1).2 (fun y => hsd.2 y) (w.under (𝓞 D.host.F))
    have hx := hP (w.under (𝓞 D.host.F)) hv w rfl
    by_cases hc : Formalism.DivisionValues.conjPl w = w
    · rw [hc]
      rcases hx with ⟨hs, -⟩ | ⟨hin, -⟩
      · exact absurd hc (conjPl_ne_of_isSplit w hs)
      · exact (GlobalTheory.LFun.ConjPlace.map_inv_of_isParamVec hin (hP _ hv w rfl)).symm
    · have hx' := hP (w.under (𝓞 D.host.F)) hv (Formalism.DivisionValues.conjPl w) (under_conjPl w)
      exact GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd (Ne.symm hc) hx hx'
  intro w hw
  have hw' : Formalism.DivisionValues.conjPl w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
    show (Formalism.DivisionValues.conjPl w).under (𝓞 D.host.F) ∉ (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))
    rw [under_conjPl]; exact hw
  have hB' : B (Formalism.DivisionValues.conjPl w) = (B w).map (·⁻¹) := GlobalTheory.T.firstMemberParameter_inv_of_chainParameter_inv D c htw.com j hj B w hw (key w hw)
  have e : GlobalTheory.ChainNS.invFam B w = B (Formalism.DivisionValues.conjPl w) := hB'.symm
  rw [e]
  have h2 := hB (Formalism.DivisionValues.conjPl w) hw'
  rwa [absNorm_conjPl'] at h2
