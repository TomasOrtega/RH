import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisTwistedNormGLBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjOfIsConjGlFieldExtensionInclusionStatement
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

open Polynomial SemidirectProduct in
open scoped Classical in
/- English proof (translation)
Take `⟨c, rfl⟩` from `isConj_iff.mp h`. Use `hf a c⁻¹` as an intermediate fact. Rewrite `this` using `[inv_inv]`. Conclude with `this.symm`.
-/
private lemma isCl_apply_eq_of_isConj {G : Type} [Group G] {f : G → ℂ}
    (hf : _root_.GlobalTheory.Shin.IsCl f) {a b : G} (h : IsConj a b) : f a = f b := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp h
  have := hf a c⁻¹
  rw [inv_inv] at this
  exact this.symm

open Polynomial SemidirectProduct in
open scoped Classical in

/- English proof (translation)
Introduce `F F' _ _ _ _ s hs n f hf`. Establish `hconj` using `(_root_.GlobalTheory.Shin.NrmBasic.main F F' s hs n).2.2.1`. Use `⟨fun δ γ hδ => ?_, fun δ y => ?_⟩` and prove the remaining obligations. Unfold `_root_.GlobalTheory.Shin.IsNorm at hδ`. Unfold `_root_.GlobalTheory.Shin.shLift`.

Establish `hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ` using `⟨γ, hδ⟩`. Rewrite using `[dif_pos hex]`. Establish `hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ)` using `hex.choose_spec`. Conclude with `isCl_apply_eq_of_isConj hf (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _ (hspec.trans hδ.symm))`. Establish `hN : IsConj (_root_.GlobalTheory.Shin.nrm s δ) (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y))`.

Rewrite using `[hconj δ y, isConj_iff]`. Conclude with `⟨y⁻¹, by rw [inv_inv]⟩`. Unfold `_root_.GlobalTheory.Shin.shLift`. Distinguish the cases in `hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ`. Establish `hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ)` using `hex.choose_spec`.

Establish `hex' : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ` using `⟨hex.choose, hspec.trans hN⟩`. Establish `hspec' : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex'.choose) (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y))` using `hex'.choose_spec`. Rewrite using `[dif_pos hex, dif_pos hex']`. Conclude with `isCl_apply_eq_of_isConj hf (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _ (hspec'.trans (hspec.trans hN).symm))`. Establish `hex' : ¬ ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ` using `fun ⟨γ, hγ⟩ => hex ⟨γ, (show IsConj (_root_.GlobalTheory.Shin.incl F F' n γ) _ from hγ).trans hN.symm⟩`.

Rewrite using `[dif_neg hex, dif_neg hex']`.
-/
theorem _root_.GlobalTheory.Shin.shLift_isNorm_and_twisted_inv : ∀ (F F' : Type) [Field F] [Field F']
    [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) →
    ∀ (n : ℕ) (f : GL (Fin n) F → ℂ), _root_.GlobalTheory.Shin.IsCl f →
    (∀ δ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ → _root_.GlobalTheory.Shin.shLift s f δ = f γ) ∧
    ∀ δ y : GL (Fin n) F', _root_.GlobalTheory.Shin.shLift s f
      (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) = _root_.GlobalTheory.Shin.shLift s f δ := by
  intro F F' _ _ _ _ s hs n f hf
  have hconj := (_root_.GlobalTheory.Shin.NrmBasic.main F F' s hs n).2.2.1
  refine ⟨fun δ γ hδ => ?_, fun δ y => ?_⟩
  · unfold _root_.GlobalTheory.Shin.IsNorm at hδ
    unfold _root_.GlobalTheory.Shin.shLift
    have hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ := ⟨γ, hδ⟩
    rw [dif_pos hex]
    have hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ) :=
      hex.choose_spec
    exact isCl_apply_eq_of_isConj hf
      (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _ (hspec.trans hδ.symm))
  · have hN : IsConj (_root_.GlobalTheory.Shin.nrm s δ)
        (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y)) := by
      rw [hconj δ y, isConj_iff]
      exact ⟨y⁻¹, by rw [inv_inv]⟩
    unfold _root_.GlobalTheory.Shin.shLift
    by_cases hex : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s δ γ
    · have hspec : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex.choose) (_root_.GlobalTheory.Shin.nrm s δ) :=
        hex.choose_spec
      have hex' : ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ :=
        ⟨hex.choose, hspec.trans hN⟩
      have hspec' : IsConj (_root_.GlobalTheory.Shin.incl F F' n hex'.choose)
          (_root_.GlobalTheory.Shin.nrm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y)) :=
        hex'.choose_spec
      rw [dif_pos hex, dif_pos hex']
      exact isCl_apply_eq_of_isConj hf
        (_root_.GlobalTheory.Shin.isConj_of_isConj_incl F F' n _ _
          (hspec'.trans (hspec.trans hN).symm))
    · have hex' : ¬ ∃ γ, _root_.GlobalTheory.Shin.IsNorm s (y⁻¹ * δ * _root_.GlobalTheory.Shin.galAct F F' n s y) γ :=
        fun ⟨γ, hγ⟩ => hex ⟨γ, (show IsConj (_root_.GlobalTheory.Shin.incl F F' n γ) _ from hγ).trans hN.symm⟩
      rw [dif_neg hex, dif_neg hex']

end GlobalTheory.Shin
