import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsComOfOf
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsStage
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory ValuativeRel GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.AdForm GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw.ComCols

variable {D : D7}

/- English proof (translation)
Use `⟨fun PP hPP => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `(hL.Pg PP).1 hPP`. Establish `h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal` using `L.C.P.overP hk`. Rewrite using `[Nat.cast_mul]`. Use `fin_cases k`.

Conclude with `Ideal.mul_mem_right _ _ h1`. Conclude with `Ideal.mul_mem_left _ _ h1`. Use `v.isMaximal` as an intermediate fact. Take `⟨Q, hQ, hQ'⟩` from `Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal`. Set `W : Formalism.L2.DIV.Pl D.host.E` to `⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩`.

Establish `hW : W.under (𝓞 D.host.F) = v` using `HeightOneSpectrum.ext hQ'.over.symm`. Establish `hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal`. Rewrite `hv` using `[← hW]`. Establish `h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ W.asIdeal` using `hv`. Rewrite `h2` using `[map_natCast, Nat.cast_mul]`.

Conclude with `(W.isPrime.mem_or_mem h2).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩`. Take `⟨k, hk⟩` from `hk`. Establish `hS` using `GlobalTheory.ChainOnto.Model.mem_S hL (GlobalTheory.Member.exists_isInfFam_family D).choose 1 L.triv k W hk`. Unfold `GlobalTheory.ChainOnto.Com.S at hS`. Take `⟨P, hP, e⟩` from `Finset.mem_image.1 hS`.

Use `⟨P, ⟨hP, e.trans hW⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `P' ⟨hP', e'⟩`. Break down `GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (e'.trans (e.trans hW).symm) with h | h` into its components or cases. Conclude with `h`. Conclude with `absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h) (GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hP) (Or.inl hP'))`.
-/
theorem isTypePlaces_of_levCh {L : LevCh D Unit} (hL : L.Is ()) : GlobalTheory.Core.Mi.IsTypePlaces L.Pg := by
  classical
  refine ⟨fun PP hPP => ?_, fun v hv => ?_⟩
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    have h1 : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := L.C.P.overP hk
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ h1
    · exact Ideal.mul_mem_left _ _ h1
  · have := v.isMaximal
    obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    let W : Formalism.L2.DIV.Pl D.host.E := ⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩
    have hW : W.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQ'.over.symm
    have hk : ∃ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ W.asIdeal := by
      rw [← hW] at hv
      have h2 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ W.asIdeal := hv
      rw [map_natCast, Nat.cast_mul] at h2
      exact (W.isPrime.mem_or_mem h2).elim (fun h => ⟨0, h⟩) fun h => ⟨1, h⟩
    obtain ⟨k, hk⟩ := hk
    have hS := GlobalTheory.ChainOnto.Model.mem_S hL (GlobalTheory.Member.exists_isInfFam_family D).choose 1 L.triv k W hk
    unfold GlobalTheory.ChainOnto.Com.S at hS
    obtain ⟨P, hP, e⟩ := Finset.mem_image.1 hS
    refine ⟨P, ⟨hP, e.trans hW⟩, ?_⟩
    rintro P' ⟨hP', e'⟩
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq (e'.trans (e.trans hW).symm) with h | h
    · exact h
    · exact absurd (GlobalTheory.GoodPrimes.isConjPl_iff.2 h) (GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hP) (Or.inl hP'))

/- English proof (translation)
Establish `hres` using `GlobalTheory.Mem.EtaTilde.isEta_res D c.η L.C.eta hη L.C.isEta`. Establish `hS : ∀ (k : Fin 2) (Q : Formalism.L2.DIV.Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → Q.under (𝓞 D.host.F) ∈ c.S` using `fun k Q hk => by`. Use `GlobalTheory.ChainOnto.Model.mem_S hL c.θ c.ψ L.triv k Q hk` as an intermediate fact. Unfold `GlobalTheory.ChainOnto.Com.S at this ⊢`. Rewrite using `[hP]`.

Conclude with `this`. Use `⟨hθ, hψ, ⟨hη.1, GlobalTheory.Mem.TupChar.unramEverywhere hη L.C.isEta.unr, ⟨⟨_, hres⟩, fun η h a => ?_⟩, fun τ => ?_, fun j hj => ?_⟩, fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hχ j⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]`. Conclude with `GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ`. Take `⟨h1, h2⟩` from `Finset.mem_Icc.1 hj`.

Take `⟨i, rfl⟩ : ∃ i, j = i + 1` from `⟨j - 1, by omega⟩`. Establish `hi : i < D.R.m` using `by omega`. Use `⟨(hμ ⟨i, hi⟩).1, ⟨_, hres⟩, fun η _ a => ?_⟩` and prove the remaining obligations. Use `show c.μ (i + 1) (idF D a) = _`. Rewrite using `[pow_zero]`.

Conclude with `GlobalTheory.GridWeil.triv_base (hμ ⟨i, hi⟩) (L.C.isMu0 ⟨i, hi⟩).triv a`. Establish `h1` using `GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (L.C.isMu0 j).inf) τ`. Simplify using `only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1`. Conclude with `h1`. Conclude with `(GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((L.C.isMu0 j).unr w fun k hk => hw (hS k w hk))`.

Rewrite using `[hP]`. Conclude with `GlobalTheory.CentralShift.exists_idemSum _ fun Q hQ Q' hQ' => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hQ) (Or.inl hQ')`.
-/
theorem com_is_of_levCh {L : LevCh D Unit} (hL : L.Is ()) (c : GlobalTheory.ChainOnto.Com D) (hθ : IsInfFam c.θ) (hψ : IsStdChar D c.ψ (-1))
    (hP : c.Pg = L.Pg) (hμ : ∀ j : Fin D.R.m, ChrEq (c.μ ((j : ℕ) + 1)) (L.C.mu0 j)) (hη : ChrEq c.η L.C.eta)
    (hχ : ∀ j : Fin D.R.m, ∀ PP ∈ c.Pg, IsRes (L.C.mu0 j) PP (c.chi ((j : ℕ) + 1) PP)⁻¹) : c.Is := by
  have hres := GlobalTheory.Mem.EtaTilde.isEta_res D c.η L.C.eta hη L.C.isEta
  have hS : ∀ (k : Fin 2) (Q : Formalism.L2.DIV.Pl D.host.E), ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal →
      Q.under (𝓞 D.host.F) ∈ c.S := fun k Q hk => by
    have := GlobalTheory.ChainOnto.Model.mem_S hL c.θ c.ψ L.triv k Q hk
    unfold GlobalTheory.ChainOnto.Com.S at this ⊢
    rw [hP]
    exact this
  refine ⟨hθ, hψ, ⟨hη.1, GlobalTheory.Mem.TupChar.unramEverywhere hη L.C.isEta.unr, ⟨⟨_, hres⟩, fun η h a => ?_⟩, fun τ => ?_,
    fun j hj => ?_⟩, fun j τ => ?_, fun j w hw => ?_, fun j => ⟨_, hμ j, hχ j⟩, ?_⟩
  · rw [(GlobalTheory.IdeleNormChar.existsUnique_isEta D).unique h hres, pow_one, MonoidHom.comp_apply]
  · exact GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hη
      (GlobalTheory.InnerSteps.hasInfQ_tauE (a := fun _ => 1 / 2) ⟨fun _ => 1, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  · obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hi : i < D.R.m := by omega
    refine ⟨(hμ ⟨i, hi⟩).1, ⟨_, hres⟩, fun η _ a => ?_⟩
    show c.μ (i + 1) (idF D a) = _
    rw [pow_zero]
    exact GlobalTheory.GridWeil.triv_base (hμ ⟨i, hi⟩) (L.C.isMu0 ⟨i, hi⟩).triv a
  · have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hμ j) (GlobalTheory.InnerSteps.hasInfQ_tauE (L.C.isMu0 j).inf) τ
    simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
    exact h1
  · exact (GlobalTheory.LFun.unrAt_iff_of_chrEq (hμ j) w).2 ((L.C.isMu0 j).unr w fun k hk => hw (hS k w hk))
  · rw [hP]
    exact GlobalTheory.CentralShift.exists_idemSum _ fun Q hQ Q' hQ' => GlobalTheory.HeckeCharacterRestriction.not_isConjPl_union hL () (Or.inl hQ) (Or.inl hQ')

end GlobalTheory.SeeSaw.ComCols
