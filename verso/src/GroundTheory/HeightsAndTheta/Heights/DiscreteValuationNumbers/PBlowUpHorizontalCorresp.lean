import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBlowUpHorizontal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Rewrite using `[finsum_mem_def, Set.indicator_eq_self.2 h]`.
-/
theorem finsum_eq_finsum_mem_of_support_subset' {α : Type*} (f : α → ℤ) {s : Set α}
    (h : Function.support f ⊆ s) : ∑ᶠ i, f i = ∑ᶠ i ∈ s, f i := by
  rw [finsum_mem_def, Set.indicator_eq_self.2 h]

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP`. Establish `sat` using `hsat O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP`. Establish `mult` using `hmult O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP`. Establish `lift` using `hlift O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP`. Establish `strict` using `hstrict O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP`.

Establish `hC : ∀ W : Ideal (MRing (extIdx ι J) O), (C ϖ : MRing ι O) ∈ W.comap (liftForm (ι` using `ι) (J := J) (R := O)) ↔ (C ϖ : MRing (extIdx ι J) O) ∈ W := by`. Introduce `W`. Rewrite using `[Ideal.mem_comap]`. Simplify using `[liftForm]`. Use `⟨fun h => ?_, fun W hW hϖW => ⟨by rw [mult W hW hϖW]; exact hW, strict W hW hϖW⟩⟩` and prove the remaining obligations.

Unfold `cycEval`. Set `s : Set (Ideal (MRing (extIdx ι J) O))` to `{W | divCycle (blowUpOf P u) (liftForm x) W ≠ 0 ∧ (C ϖ : MRing (extIdx ι J) O) ∉ W}`. Set `t : Set (Ideal (MRing ι O))` to `{W | divCycle P x W ≠ 0 ∧ (C ϖ : MRing ι O) ∉ W}`. Rewrite using `[finsum_eq_finsum_mem_of_support_subset' _ (s := s) ?hs, finsum_eq_finsum_mem_of_support_subset' _ (s := t) ?ht]`. Use `case hs =>`.

Introduce `W hW`. Rewrite `hW` using `[Function.mem_support]`. Conclude with `⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩`. Use `case ht =>`. Introduce `W hW`.

Rewrite `hW` using `[Function.mem_support]`. Conclude with `⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩`. Use `finsum_mem_eq_of_bijOn (fun W => W.comap (liftForm (ι := ι) (J := J) (R := O))) ⟨?_, ?_, ?_⟩ ?_` and prove the remaining obligations. Introduce `W hW`. Conclude with `⟨by rw [mult W hW.1 hW.2]; exact hW.1, fun h => hW.2 ((hC W).1 h)⟩`.

Introduce `W₁ h₁ W₂ h₂ he`. Use extensionality with `F`. Rewrite using `[sat W₁ h₁.1 h₁.2 F, sat W₂ h₂.1 h₂.2 F]`. Simplify using `only at he`. Rewrite using `[he]`.

Introduce `W hW`. Take `⟨W', h1, h2, h3⟩` from `lift W hW.1 hW.2`. Conclude with `⟨W', ⟨h1, h2⟩, h3⟩`. Introduce `W hW`. Simplify using `only`.

Rewrite using `[if_neg hW.2, if_neg (fun h => hW.2 ((hC W).1 h)), mult W hW.1 hW.2]`.
-/
theorem BlowUpHorizontalCorresp.proof (hsat : BlowUpHorizontalSat.Statement.{u})
    (hmult : BlowUpHorizontalMult.Statement.{u}) (hlift : BlowUpHorizontalLift.Statement.{u})
    (hstrict : BlowUpHorizontalStrict.Statement.{u}) : BlowUpHorizontalCorresp.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ J _ P n hP N u hu hex hloc c x hx hxP
  have sat := hsat O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have mult := hmult O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have lift := hlift O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have strict := hstrict O ϖ hϖ K ι J P n hP N u hu hex hloc c x hx hxP
  have hC : ∀ W : Ideal (MRing (extIdx ι J) O),
      (C ϖ : MRing ι O) ∈ W.comap (liftForm (ι := ι) (J := J) (R := O)) ↔
        (C ϖ : MRing (extIdx ι J) O) ∈ W := by
    intro W
    rw [Ideal.mem_comap]
    simp [liftForm]
  refine ⟨fun h => ?_, fun W hW hϖW => ⟨by rw [mult W hW hϖW]; exact hW, strict W hW hϖW⟩⟩
  classical
  unfold cycEval
  let s : Set (Ideal (MRing (extIdx ι J) O)) :=
    {W | divCycle (blowUpOf P u) (liftForm x) W ≠ 0 ∧ (C ϖ : MRing (extIdx ι J) O) ∉ W}
  let t : Set (Ideal (MRing ι O)) := {W | divCycle P x W ≠ 0 ∧ (C ϖ : MRing ι O) ∉ W}
  rw [finsum_eq_finsum_mem_of_support_subset' _ (s := s) ?hs,
    finsum_eq_finsum_mem_of_support_subset' _ (s := t) ?ht]
  case hs =>
    intro W hW
    rw [Function.mem_support] at hW
    exact ⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩
  case ht =>
    intro W hW
    rw [Function.mem_support] at hW
    exact ⟨fun h0 => hW (by rw [h0, zero_mul]), fun hc => hW (by simp only [if_pos hc, mul_zero])⟩
  refine finsum_mem_eq_of_bijOn (fun W => W.comap (liftForm (ι := ι) (J := J) (R := O)))
    ⟨?_, ?_, ?_⟩ ?_
  · intro W hW
    exact ⟨by rw [mult W hW.1 hW.2]; exact hW.1, fun h => hW.2 ((hC W).1 h)⟩
  · intro W₁ h₁ W₂ h₂ he
    ext F
    rw [sat W₁ h₁.1 h₁.2 F, sat W₂ h₂.1 h₂.2 F]
    simp only at he
    rw [he]
  · intro W hW
    obtain ⟨W', h1, h2, h3⟩ := lift W hW.1 hW.2
    exact ⟨W', ⟨h1, h2⟩, h3⟩
  · intro W hW
    simp only
    rw [if_neg hW.2, if_neg (fun h => hW.2 ((hC W).1 h)), mult W hW.1 hW.2]

end GroundTheory.Heights₂.Heights.NumbersDVR
