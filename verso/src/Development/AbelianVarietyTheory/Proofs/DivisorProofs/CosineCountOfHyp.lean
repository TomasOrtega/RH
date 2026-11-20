import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfCountAtOf
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePartBase

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SumSize GlobalTheory.SumCount

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.CosCount

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

/- English proof (translation)
Establish `hs : 1 ≤ (locGrid G t P).s` using `one_le_sLen`. Establish `hkeep : keepAt G P = false` using `by simp [keepAt, hP]`. Establish `hdep : depthAt G P = cosExp G P`. Take `⟨v, hv, rfl⟩` from `Finset.mem_image.1 hP`. Take `⟨h1, h2⟩` from `depthAt_w G hv`.

Rewrite using `[h1, h2]`. Establish `hm : 0 < D.R.m` using `by have := D.R.two_le_m; omega`. Establish `h00` using `((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm`. Use `haveI := (isUnitVol_unitVol P).1`. Establish `hT` using `isTensor_Tflip hL W S.B t Φ hde hc hl`.

Rewrite `hT` using `[hdep]`. Establish `hO` using `oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even (isUnif_unifAt P) h00.cond hT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO G t P hj)`. Establish `hk : keepAt G (⟨P, hl⟩ : locPl G t).1 = false` using `hkeep`. Establish `hb` using `hβ ⟨P, hl⟩`. Establish `hb2` using `hβ' ⟨P, hl⟩`.

Rewrite `hb`, `hb2` using `[hk]`. Conclude with `funext fun i => (hO _ hb i).trans (hO _ hb2 i).symm`.
-/
theorem cosFam_apply_eq_of_mem_supp {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) {P : Pl D.host.E} (hP : P ∈ G.pl.W0)
    (hl : P ∈ locPl G t) {β β' : CosFam G t} (hβ : β ∈ S.supp t Φ) (hβ' : β' ∈ S.supp t Φ) :
    β ⟨P, hl⟩ = β' ⟨P, hl⟩ := by
  classical
  have hs : 1 ≤ (locGrid G t P).s := one_le_sLen
  have hkeep : keepAt G P = false := by simp [keepAt, hP]
  have hdep : depthAt G P = cosExp G P := by
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hP
    obtain ⟨h1, h2⟩ := depthAt_w G hv
    rw [h1, h2]
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := ((Good.locGrid_isGood hL G W t hde hc).1 P hl).square 0 hm 0 hm
  haveI := (isUnitVol_unitVol P).1
  have hT := isTensor_Tflip hL W S.B t Φ hde hc hl
  rw [hdep] at hT
  have hO := oneCoset hs (psiAt W P) (unitVol P) (givenLevel G t P) (Tflip W S.B t Φ P) (unifAt P) (cosExp G P) D.R.m_even
    (isUnif_unifAt P) h00.cond hT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO G t P hj)
  have hk : keepAt G (⟨P, hl⟩ : locPl G t).1 = false := hkeep
  have hb := hβ ⟨P, hl⟩
  have hb2 := hβ' ⟨P, hl⟩
  rw [hk] at hb hb2
  exact funext fun i => (hO _ hb i).trans (hO _ hb2 i).symm

/- English proof (translation)
Introduce `β hβ β' hβ'`. Establish `hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Introduce `P hP`. Rewrite `hP` using `[hQ]`. Conclude with `absurd hP (Finset.notMem_empty _)`.

Use function extensionality and compare the values at `⟨P, hl⟩`. Establish `hP : P ∈ G.pl.W0`. Break down `Finset.mem_union.1 hl with h | h` into its components or cases. Conclude with `h`. Rewrite `h` using `[hQ]`.

Conclude with `absurd h (Finset.notMem_empty _)`. Conclude with `cosFam_apply_eq_of_mem_supp hL S t Φ hde hc hP hl hβ hβ'`.
-/
theorem supp_subsingleton {μ₀ : T} (hL : L.Is μ₀) (S : GridChoice W U) (t : T) (Φ : G.Datum)
    (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) (hQ : L.Q t = ∅) : (S.supp t Φ).Subsingleton := by
  classical
  intro β hβ β' hβ'
  have hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    intro P hP; rw [hQ] at hP; exact absurd hP (Finset.notMem_empty _)
  funext ⟨P, hl⟩
  have hP : P ∈ G.pl.W0 := by
    rcases Finset.mem_union.1 hl with h | h
    · exact h
    · rw [hQ] at h; exact absurd h (Finset.notMem_empty _)
  exact cosFam_apply_eq_of_mem_supp hL S t Φ hde hc hP hl hβ hβ'

/- English proof (translation)
Introduce `_`. Use `⟨0, fun CF _ => ⟨0, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => ?_⟩⟩⟩` and prove the remaining obligations. Introduce `Φ`. Establish `hL` using `s.core.lev`. Establish `hde` using `GlobalTheory.RowClaim.Test.pde_ne_q s`.

Establish `hQ` using `GlobalTheory.LiftLower.Q_base hL`. Establish `hsub : (ch.S.supp A.μ0 Φ).Subsingleton` using `supp_subsingleton hL ch.S.toGridChoice A.μ0 Φ hde hQ`. Establish `h1 : ((ch.S.supp A.μ0 Φ).ncard : ℝ) ≤ 1` using `by haveI : Finite (ch.S.supp A.μ0 Φ) := hsub.finite.to_subtype`. Conclude with `Set.ncard_le_one_iff_subsingleton.mpr hsub` after adjusting the coercions. Establish `hb : 1 ≤ large₂.sc.b` using `Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)`.

Establish `hX` using `ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.sig_nonneg ch.G`. Establish `hlog : 0 ≤ Real.log large₂.sc.b` using `Real.log_nonneg hb`. Establish `ha : 0 ≤ (D.R.m : ℝ) * aOne ch.G C large₂.sc.b`. Unfold `aOne`. Establish `: (0 : ℝ) ≤ C` using `hC`.

Check the signs of the components of the expression. Conclude with `h1.trans (Real.one_le_exp ha)`.
-/
theorem cosK : GlobalTheory.FunPr.Hypotheses₂ → CosK := by
  intro _
  refine ⟨0, fun CF _ => ⟨0, fun ε C hC => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ _ => ?_⟩⟩⟩
  intro Φ
  have hL := s.core.lev
  have hde := GlobalTheory.RowClaim.Test.pde_ne_q s
  have hQ := GlobalTheory.LiftLower.Q_base hL
  have hsub : (ch.S.supp A.μ0 Φ).Subsingleton := supp_subsingleton hL ch.S.toGridChoice A.μ0 Φ hde hQ
  have h1 : ((ch.S.supp A.μ0 Φ).ncard : ℝ) ≤ 1 := by
    haveI : Finite (ch.S.supp A.μ0 Φ) := hsub.finite.to_subtype
    exact_mod_cast Set.ncard_le_one_iff_subsingleton.mpr hsub
  have hb : 1 ≤ large₂.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _)
  have hX := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.sig_nonneg ch.G
  have hlog : 0 ≤ Real.log large₂.sc.b := Real.log_nonneg hb
  have ha : 0 ≤ (D.R.m : ℝ) * aOne ch.G C large₂.sc.b := by
    unfold aOne
    have : (0 : ℝ) ≤ C := hC
    positivity
  exact h1.trans (Real.one_le_exp ha)

end GlobalTheory.CosCount
