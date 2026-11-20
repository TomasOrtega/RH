import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffHeckePolyOfComplex
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSupSt

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.FWT
  Formalism.L2.Pj GlobalTheory.HeckeParts

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

/- English proof (translation)
Take `⟨c, hβ⟩` from `hL.βW i`. Establish `hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal`. Rewrite using `[one_pow, Nat.cast_one]`. Conclude with `(Ideal.ne_top_iff_one _).1 P.isPrime.ne_top`. Establish `hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P`.

Introduce `PP hPP`. Establish `hPP' : PP ∈ R.Pg` using `hPP.elim id fun h => absurd h (Finset.notMem_empty _)`. Establish `hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))` using `hF.Sb hPP'`. Use `⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩` and prove the remaining obligations. Rewrite using `[Formalism.L2.Col.conjIdeal_asIdeal]`.

Use `PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_` and prove the remaining obligations. Take `⟨a', ha', e⟩` from `h a ha`. Rewrite using `[Formalism.L2.Col.mem_conjP]`. Establish `: Formalism.L2.Col.cO D.host.E a = a'` using `RingOfIntegers.ext e.symm`. Rewrite using `[this]` and apply the resulting hypothesis.

Take `⟨e, he⟩` from `GlobalTheory.MovedIdem.exists_isIdemAt P hso.1`. Take `⟨ϖ, h1, h2⟩` from `SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)`. Take `⟨-, hrep, hel⟩` from `GlobalTheory.SplitPlace.split_local (Wc D i) P e he`. Take `⟨α, hα⟩` from `(hel ϖ h1 h2).1 k (hk.trans (r_le_rank_Wc i))`. Take `⟨Lp, hLp, -, hs, hK⟩` from `loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he`.

Take `⟨Rc, hA, h3, h4⟩` from `hrep α hα.2.1`. Conclude with `⟨α, Rc, ⟨e, ϖ, he, h1, h2, hα⟩, isDC_of_splits hs levG_le_flag ((hLp α).2 hα.2.1) (fun a ha => (hLp a).2 (hA a ha)) hK (fun γ hγ => (h3 γ hγ).2) h4⟩`.
-/
theorem exists_heckeElt {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (hL : R.toLevCh.Is A.μ0) (hF : R.IsFam) (i : Fin D.R.m) {P : Formalism.L2.DIV.Pl D.host.E}
    (hso : Bridge.SplitOff P (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E))) {k : ℕ} (hk : k ≤ D.R.r) :
    ∃ α Rc, IsHeckeAt (Wc D i) P k α ∧ Bridge.IsDC (levG (Wc D i) (R.βW i) (R.datWp i R.triv)) α Rc := by
  obtain ⟨c, hβ⟩ := hL.βW i
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hF.Sb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hso.1
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  obtain ⟨-, hrep, hel⟩ := GlobalTheory.SplitPlace.split_local (Wc D i) P e he
  obtain ⟨α, hα⟩ := (hel ϖ h1 h2).1 k (hk.trans (r_le_rank_Wc i))
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ (L := R.datWp i R.triv) ⟨hso.1, hN, hoff⟩ he
  obtain ⟨Rc, hA, h3, h4⟩ := hrep α hα.2.1
  exact ⟨α, Rc, ⟨e, ϖ, he, h1, h2, hα⟩, isDC_of_splits hs levG_le_flag ((hLp α).2 hα.2.1) (fun a ha => (hLp a).2 (hA a ha)) hK
    (fun γ hγ => (h3 γ hγ).2) h4⟩

end GlobalTheory.HeckeSupSt
