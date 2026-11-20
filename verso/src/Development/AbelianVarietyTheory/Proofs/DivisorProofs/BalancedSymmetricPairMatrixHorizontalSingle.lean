import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLieCombIffIsCombAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetFrameChangeBalancedTensorsCmType
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogKSDiv.PairEntry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

/- English proof (translation)
Simplify using `[psiSet]`.
-/
theorem mem_psiSet_iff (τ : E →+* ℂ) : τ ∈ psiSet H ↔ τ (H.rt : E) = H.rt0 := by
  simp [psiSet]

def pairToH : GlobalTheory.LogKSDiv.PairIx H Dw ≃ HIx Dw (psiSet H) where
  toFun P := ⟨⟨P.1.1, (mem_psiSet_iff _).2 P.1.2⟩, P.2.2, P.2.1⟩
  invFun k := ⟨⟨k.1.1, (mem_psiSet_iff _).1 k.1.2⟩, k.2.2, k.2.1⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/- English proof (translation)
Take `⟨⟨τ, hτ⟩, i, k'⟩` from `P`. Take `⟨⟨σ, hσ⟩, a, b⟩` from `k`. Establish `hσ' : σ (H.rt : E) = H.rt0` using `(mem_psiSet_iff _).1 hσ`. Establish `h2 : ¬ (e ⟨σ, b⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩ ∧ e ⟨conjEmb σ, a⟩ = e ⟨τ, i⟩)`. Introduce and unpack `⟨h, -⟩`.

Establish `h5 : σ = (starRingEnd ℂ).comp τ` using `congrArg Sigma.fst (e.injective h)`. Conclude with `GlobalTheory.LogKSDiv.DetChange.conj_off H τ hτ (h5 ▸ hσ')`. Simplify using `only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]`. Rewrite using `[if_neg h2, add_zero]`. Distinguish the cases in `h : τ = σ`.

Substitute `h` using the available equality. Establish `key : (e ⟨τ, b⟩ = e ⟨τ, i⟩ ∧ e ⟨conjEmb τ, a⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩) ↔ pairToH (Dw` using `Dw) ⟨⟨τ, hτ⟩, (i, k')⟩ = ⟨⟨τ, hσ⟩, (a, b)⟩ := by`. Simplify using `only [e.apply_eq_iff_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`.

Establish `hb : b = i` using `eq_of_heq (Sigma.mk.inj_iff.1 h1).2`. Establish `ha : a = k'` using `eq_of_heq (Sigma.mk.inj_iff.1 h2).2`. Substitute `hb ha` using the available equality. Both sides reduce to the same expression. Introduce `h4`.

Establish `h5` using `(Sigma.mk.inj_iff.1 h4).2`. Simplify using `only [heq_iff_eq, Prod.mk.injEq] at h5`. Take `⟨rfl, rfl⟩` from `h5`. Conclude with `⟨rfl, rfl⟩`. Conclude with `if_congr key rfl rfl`.

Establish `h3 : ¬ (e ⟨σ, b⟩ = e ⟨τ, i⟩ ∧ e ⟨conjEmb σ, a⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩)`. Introduce and unpack `⟨h4, -⟩`. Conclude with `h (congrArg Sigma.fst (e.injective h4)).symm`. Rewrite using `[if_neg h3, if_neg]`. Introduce `h4`.

Conclude with `h (congrArg (fun x : HIx Dw (psiSet H) => x.1.1) h4)`.
-/
theorem symPair_entry {R : Type} [CommRing R] {n : ℕ} (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n)
    (P : GlobalTheory.LogKSDiv.PairIx H Dw) (k : HIx Dw (psiSet H)) :
    GlobalTheory.LogKSDiv.symPair (R := R) e P (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩) =
      if pairToH P = k then 1 else 0 := by
  obtain ⟨⟨τ, hτ⟩, i, k'⟩ := P
  obtain ⟨⟨σ, hσ⟩, a, b⟩ := k
  have hσ' : σ (H.rt : E) = H.rt0 := (mem_psiSet_iff _).1 hσ
  have h2 : ¬ (e ⟨σ, b⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩ ∧ e ⟨conjEmb σ, a⟩ = e ⟨τ, i⟩) := by
    rintro ⟨h, -⟩
    have h5 : σ = (starRingEnd ℂ).comp τ := congrArg Sigma.fst (e.injective h)
    exact GlobalTheory.LogKSDiv.DetChange.conj_off H τ hτ (h5 ▸ hσ')
  simp only [GlobalTheory.LogKSDiv.symPair, Matrix.of_apply]
  rw [if_neg h2, add_zero]
  by_cases h : τ = σ
  · subst h
    have key : (e ⟨τ, b⟩ = e ⟨τ, i⟩ ∧ e ⟨conjEmb τ, a⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩) ↔
        pairToH (Dw := Dw) ⟨⟨τ, hτ⟩, (i, k')⟩ = ⟨⟨τ, hσ⟩, (a, b)⟩ := by
      simp only [e.apply_eq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩
        have hb : b = i := eq_of_heq (Sigma.mk.inj_iff.1 h1).2
        have ha : a = k' := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
        subst hb ha
        rfl
      · intro h4
        have h5 := (Sigma.mk.inj_iff.1 h4).2
        simp only [heq_iff_eq, Prod.mk.injEq] at h5
        obtain ⟨rfl, rfl⟩ := h5
        exact ⟨rfl, rfl⟩
    exact if_congr key rfl rfl
  · have h3 : ¬ (e ⟨σ, b⟩ = e ⟨τ, i⟩ ∧ e ⟨conjEmb σ, a⟩ = e ⟨(starRingEnd ℂ).comp τ, k'⟩) := by
      rintro ⟨h4, -⟩
      exact h (congrArg Sigma.fst (e.injective h4)).symm
    rw [if_neg h3, if_neg]
    intro h4
    exact h (congrArg (fun x : HIx Dw (psiSet H) => x.1.1) h4)

end GlobalTheory.LogKSDiv.PairEntry

namespace GlobalTheory.LogKSDiv.PairEntry

/- English proof (translation)
Introduce `E _ _ _ H Dw ε`. Use `⟨ε.trans pairToH, fun f n e j k => ?_⟩` and prove the remaining obligations. Rewrite using `[symPair_entry, Pi.single_apply, Equiv.trans_apply]`. Distinguish the cases in `h : pairToH (ε j) = k`. Rewrite using `[if_pos h, if_pos h.symm, map_one]`.

Rewrite using `[if_neg h, if_neg (Ne.symm h), map_zero]`.
-/
theorem symPair_horizontal_single : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw), ∃ κ : Fin Dw.dim ≃ HIx Dw (psiSet H), ∀ {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (j : Fin Dw.dim) (k : HIx Dw (psiSet H)), f (GlobalTheory.LogKSDiv.symPair (R := R) e (ε j) (e ⟨k.1.1, k.2.2⟩) (e ⟨conjEmb k.1.1, k.2.1⟩)) = (Pi.single (κ j) (1 : S) : HIx Dw (psiSet H) → S) k := by
  intro E _ _ _ H Dw ε
  refine ⟨ε.trans pairToH, fun f n e j k => ?_⟩
  rw [symPair_entry, Pi.single_apply, Equiv.trans_apply]
  by_cases h : pairToH (ε j) = k
  · rw [if_pos h, if_pos h.symm, map_one]
  · rw [if_neg h, if_neg (Ne.symm h), map_zero]

end GlobalTheory.LogKSDiv.PairEntry
