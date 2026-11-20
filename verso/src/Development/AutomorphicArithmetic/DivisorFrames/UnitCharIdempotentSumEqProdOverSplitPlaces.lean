import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.FinMatchDefs
import Development.AutomorphicArithmetic.DivisorFrames.UnitCharIdempotentSumEqProdUnitInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Take `⟨⟨es, h, rfl⟩, -⟩` from `he`. Rewrite using `[map_sum (toEAf D), map_sum (GlobalTheory.StdFrames.cpt (D := D) w), Finset.sum_eq_single_of_mem w hw fun Q hQ hne => (GlobalTheory.StdFrames.cpt_of_isIdemAt (h Q hQ)).2 w hne.symm]`. Conclude with `(GlobalTheory.StdFrames.cpt_of_isIdemAt (h w hw)).1`.
-/
private theorem cpt_sum {D : D7} {e : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (he : IsIdemSum e S)
    {w : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ S) : GlobalTheory.StdFrames.cpt (D := D) w (toEAf D e) = 1 := by
  obtain ⟨⟨es, h, rfl⟩, -⟩ := he
  rw [map_sum (toEAf D), map_sum (GlobalTheory.StdFrames.cpt (D := D) w),
    Finset.sum_eq_single_of_mem w hw fun Q hQ hne => (GlobalTheory.StdFrames.cpt_of_isIdemAt (h Q hQ)).2 w hne.symm]
  exact (GlobalTheory.StdFrames.cpt_of_isIdemAt (h w hw)).1

/- English proof (translation)
Break down `GlobalTheory.IdemSupport.eq_or_eq_cP h with h1 | h1` into its components or cases. Conclude with `h1`. It suffices to derive a contradiction. Establish `h0 : toEAf D e * GlobalTheory.StdFrames.sg D (toEAf D e) = 0`. Rewrite using `[← GlobalTheory.StdFrames.toEAf_cA, ← RingHom.map_mul, he.2, RingHom.map_zero]`.

Establish `h2 : GlobalTheory.StdFrames.cpt (D` using `D) (GlobalTheory.IdemSupport.cP w') (1 - toEAf D e) = 0 := by`. Rewrite using `[← h1, RingHom.map_sub, RingHom.map_one, cpt_sum he hw, sub_self]`. Establish `h3` using `GlobalTheory.StdFrames.cpt_sg_eq_zero h2`. Establish `h4` using `congrArg (GlobalTheory.StdFrames.cpt (D := D) w') h0`. Rewrite `h4` using `[RingHom.map_mul, RingHom.map_zero, cpt_sum he hw', one_mul]`.

Rewrite `h3` using `[RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, h4, sub_zero]`. Conclude with `one_ne_zero h3`.
-/
private theorem no_conj {D : D7} {e : AE D} {S : Finset (HeightOneSpectrum (𝓞 D.host.E))} (he : IsIdemSum e S)
    {w w' : HeightOneSpectrum (𝓞 D.host.E)} (hw : w ∈ S) (hw' : w' ∈ S)
    (h : w.under (𝓞 D.host.F) = w'.under (𝓞 D.host.F)) : w = w' := by
  rcases GlobalTheory.IdemSupport.eq_or_eq_cP h with h1 | h1
  · exact h1
  · exfalso
    have h0 : toEAf D e * GlobalTheory.StdFrames.sg D (toEAf D e) = 0 := by
      rw [← GlobalTheory.StdFrames.toEAf_cA, ← RingHom.map_mul, he.2, RingHom.map_zero]
    have h2 : GlobalTheory.StdFrames.cpt (D := D) (GlobalTheory.IdemSupport.cP w') (1 - toEAf D e) = 0 := by
      rw [← h1, RingHom.map_sub, RingHom.map_one, cpt_sum he hw, sub_self]
    have h3 := GlobalTheory.StdFrames.cpt_sg_eq_zero h2
    have h4 := congrArg (GlobalTheory.StdFrames.cpt (D := D) w') h0
    rw [RingHom.map_mul, RingHom.map_zero, cpt_sum he hw', one_mul] at h4
    rw [RingHom.map_sub, RingHom.map_one, RingHom.map_sub, RingHom.map_one, h4, sub_zero] at h3
    exact one_ne_zero h3

/- English proof (translation)
Take `⟨y, rfl⟩` from `(Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).surjective z`. Take `⟨e, he, -⟩` from `GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E`. Take `⟨a, ha⟩` from `e.surjective (0, y)`. Establish `h2 : finPart D a = y`. Establish `: (e a).2 = finPart D a` using `(he a).2`.

Rewrite using `[← this, ha]`. Rewrite using `[← h2]`. Conclude with `(GlobalTheory.BotMatch.evW_toEAf τ a).trans (piF_toEAf τ a).symm`.
-/
private theorem evW_eq {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (z : EAf D) : GlobalTheory.BotMatch.evW τ z = piF τ z := by
  obtain ⟨y, rfl⟩ := (Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).surjective z
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  obtain ⟨a, ha⟩ := e.surjective (0, y)
  have h2 : finPart D a = y := by
    have : (e a).2 = finPart D a := (he a).2
    rw [← this, ha]
  rw [← h2]
  exact (GlobalTheory.BotMatch.evW_toEAf τ a).trans (piF_toEAf τ a).symm

/- English proof (translation)
Introduce `D e₀ S he P t hP hS ν k N hN`. Establish `hdet : N.det ∈ GlobalTheory.StdFrames.OA D`. Rewrite using `[Matrix.det_apply']`. Conclude with `sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hN _ _)`. Establish `key` using `UpperTheory.unitChar_idempotentSum_eq_prod_unitInd D e₀ S he P (fun v => v.1) t (fun w => ⟨fun hw => ?_, ?_⟩) ?_ ν k N ?_`.

Rewrite using `[key]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[evW_eq, RingHom.map_det]`. Both sides reduce to the same expression. Use `⟨⟨_, (hP _).2 ⟨w, hw, rfl⟩⟩, no_conj he (hS _) hw ?_⟩` and prove the remaining obligations.

Conclude with `GlobalTheory.AdelicU.splitPrime_under _`. Introduce and unpack `⟨v, rfl⟩`. Conclude with `hS v`. Introduce `v v' h`. Establish `h1` using `congrArg (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.under (𝓞 D.host.F)) h`.

Simplify using `only [GlobalTheory.AdelicU.splitPrime_under] at h1`. Conclude with `Subtype.ext h1`. Introduce `v`. Establish `h1` using `(GlobalTheory.StdFrames.mem_OA_iff _).1 hdet (splitPrime (t v))`. Rewrite `h1` using `[← GlobalTheory.BotMatch.complEquiv_evW, HeightOneSpectrum.mem_adicCompletionIntegers, GlobalTheory.LFun.SplitTie.complEquiv_apply, GlobalTheory.LFun.SplitTie.valued_complMap]`.

Use `haveI : (Valued.v : Valuation (v.1.adicCompletion D.host.F) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _`. Conclude with `(ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one.2 h1`.
-/
theorem UpperTheory.unitChar_idempotentSum_eq_prod_over_splitPlaces :
    ∀ (D : D7) (e₀ : AE D) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), IsIdemSum e₀ S →
        ∀ (P : Finset (HeightOneSpectrum (𝓞 D.host.F))) (t : ∀ v : P, D.host.E →ₐ[D.host.F] Fv D.host.F v),
        (∀ v, v ∈ P ↔ ∃ w ∈ S, w.under (𝓞 D.host.F) = v) → (∀ v : P, splitPrime (t v) ∈ S) →
        ∀ (ν : (AE D)ˣ →* Circle) (k : ℕ) (N : Matrix (Fin k) (Fin k) (EAf D)), IsIntM N →
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.unitChar ν e₀ N = ∏ v : P, GlobalTheory.StdPairCone.unitInd (chrW ν (t v)) (N.map (piF (t v))).det := by
  intro D e₀ S he P t hP hS ν k N hN
  have hdet : N.det ∈ GlobalTheory.StdFrames.OA D := by
    rw [Matrix.det_apply']
    exact sum_mem fun σ _ => mul_mem (intCast_mem _ _) (prod_mem fun i _ => hN _ _)
  have key := UpperTheory.unitChar_idempotentSum_eq_prod_unitInd D e₀ S he P (fun v => v.1) t (fun w => ⟨fun hw => ?_, ?_⟩) ?_ ν k N ?_
  · rw [key]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [evW_eq, RingHom.map_det]
    rfl
  · refine ⟨⟨_, (hP _).2 ⟨w, hw, rfl⟩⟩, no_conj he (hS _) hw ?_⟩
    exact GlobalTheory.AdelicU.splitPrime_under _
  · rintro ⟨v, rfl⟩
    exact hS v
  · intro v v' h
    have h1 := congrArg (fun w : HeightOneSpectrum (𝓞 D.host.E) => w.under (𝓞 D.host.F)) h
    simp only [GlobalTheory.AdelicU.splitPrime_under] at h1
    exact Subtype.ext h1
  · intro v
    have h1 := (GlobalTheory.StdFrames.mem_OA_iff _).1 hdet (splitPrime (t v))
    rw [← GlobalTheory.BotMatch.complEquiv_evW, HeightOneSpectrum.mem_adicCompletionIntegers,
      GlobalTheory.LFun.SplitTie.complEquiv_apply, GlobalTheory.LFun.SplitTie.valued_complMap] at h1
    haveI : (Valued.v : Valuation (v.1.adicCompletion D.host.F) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact (ValuativeRel.isEquiv (ValuativeRel.valuation _) Valued.v).le_one_iff_le_one.2 h1
