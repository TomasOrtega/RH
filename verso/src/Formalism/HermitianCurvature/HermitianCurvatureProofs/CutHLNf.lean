import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHL2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RdVOfEq

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

/- English proof (translation)
Rewrite using `[zfull_apply]`. Unfold `C3.Zb`. Use `a.isLt` as an intermediate fact. Use `b.isLt` as an intermediate fact. Distinguish the cases in `h1 : a.val < j ∧ b.val < j`.

Rewrite using `[dif_pos h1, dif_pos h1.1, dif_pos h1.2]`. Rewrite using `[dif_neg h1]`. Distinguish the cases in `ha : a.val < j`. Establish `hb : ¬ b.val < j` using `fun hb => h1 ⟨ha, hb⟩`. Rewrite using `[dif_pos ha, dif_neg hb, if_neg (fun h => by omega)]`.

Rewrite using `[dif_neg ha]`. Distinguish the cases in `h2 : a.val = j ∧ b.val = j`. Rewrite using `[if_pos h2, if_pos (by omega)]`. Rewrite using `[if_neg h2, if_neg (by omega)]`.
-/
theorem zfull_zb {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (a b : Fin (j + 1)) :
    zfull Z τ a b = C3.Zb j 1 Z τ a.val b.val := by
  rw [zfull_apply]
  unfold C3.Zb
  have := a.isLt; have := b.isLt
  by_cases h1 : a.val < j ∧ b.val < j
  · rw [dif_pos h1, dif_pos h1.1, dif_pos h1.2]
  · rw [dif_neg h1]
    by_cases ha : a.val < j
    · have hb : ¬ b.val < j := fun hb => h1 ⟨ha, hb⟩
      rw [dif_pos ha, dif_neg hb, if_neg (fun h => by omega)]
    · rw [dif_neg ha]
      by_cases h2 : a.val = j ∧ b.val = j
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

/- English proof (translation)
Introduce `k r j hj Z τ γ hZ hτ hγ`. Use `⟨fun a p ha => ?_, fun a p ha => ?_⟩` and prove the remaining obligations. Rewrite using `[upper_minor_of_level_point hj Z τ γ a p ha]`. Distinguish the cases in `hp : p.val < j + 1`. Rewrite using `[dif_pos hp, if_pos hp]`.

Conclude with `zfull_zb Z τ _ _`. Rewrite using `[dif_neg hp, if_neg hp]`. Rewrite using `[lower_minor_of_level_point hj hZ hτ hγ a p ha]`. Distinguish the cases in `hp : r + k < p.val ∧ 2 * r + k - p.val < j + 1`. Rewrite using `[dif_pos hp, if_pos hp]`.

Conclude with `congrArg star (zfull_zb Z τ _ _)`. Rewrite using `[dif_neg hp, if_neg hp]`.
-/
theorem normal_form_x0 : NormalFormsAtBasePoint := by
  intro k r j hj Z τ γ hZ hτ hγ
  refine ⟨fun a p ha => ?_, fun a p ha => ?_⟩
  · rw [upper_minor_of_level_point hj Z τ γ a p ha]
    by_cases hp : p.val < j + 1
    · rw [dif_pos hp, if_pos hp]
      exact zfull_zb Z τ _ _
    · rw [dif_neg hp, if_neg hp]
  · rw [lower_minor_of_level_point hj hZ hτ hγ a p ha]
    by_cases hp : r + k < p.val ∧ 2 * r + k - p.val < j + 1
    · rw [dif_pos hp, if_pos hp]
      exact congrArg star (zfull_zb Z τ _ _)
    · rw [dif_neg hp, if_neg hp]

/- English proof (translation)
Introduce `k r j hj z z' Z τ γ hZ hτ hγ`. Establish `hnf` using `(normal_form_x0 k r j hj Z τ γ hZ hτ hγ).1`. Establish `hd` using `Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb j 1 Z τ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[PBG.dmin_nf z z' _ j 1 Z τ hj hnf j (by omega), hd.1]`.

Rewrite using `[PBG.dmin_nf z z' _ j 1 Z τ hj hnf (j + 1) le_rfl, hd.2]`. Simplify using `[C3.sgnW]`.
-/
theorem leading_minors_at_base_point : LeadingMinorsAtBasePoint := by
  intro k r j hj z z' Z τ γ hZ hτ hγ
  have hnf := (normal_form_x0 k r j hj Z τ γ hZ hτ hγ).1
  have hd := Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb j 1 Z τ
  refine ⟨?_, ?_⟩
  · rw [PBG.dmin_nf z z' _ j 1 Z τ hj hnf j (by omega), hd.1]
  · rw [PBG.dmin_nf z z' _ j 1 Z τ hj hnf (j + 1) le_rfl, hd.2]
    simp [C3.sgnW]

/- English proof (translation)
Introduce `hNf k r j hj z z' E _ _ Dm Φ Z γ τ hH Y`. Take `⟨hz, hz', hD, hDs, hR, hZ, hτ, hγ, hx⟩` from `hH`. Take `⟨hnf, hnfy⟩` from `hNf k r j hj Z τ γ hZ hτ hγ`. Establish `hxG : x0 k r j hj Z τ γ ∈ B.GV k r` using `x0_GV hj hZ hτ hγ`. Establish `hx1 : x0 k r j hj Z τ γ ∈ Q.Glev k r 0 ∩ Dm` using `⟨⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hx⟩`.

Establish `hK : Q.SmoothLev k r 0 Dm Φ` using `hR.1`. Establish `hRule : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g` using `fun g hg p q hpq => Formalism.FourierDecayAlt.P.rule_of_eq E k r z' Φ g hz' (fun n hn => (hR.2.1 g hg n hn).2) p q hpq`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h` using `PBG.letter_plus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hnf Φ hK hRule Y`. Rewrite `h` using `[show ((-1 : ℂ) ^ (1 - 1) * τ⁻¹) = τ⁻¹ by simp]`.

Conclude with `h`. Establish `h` using `PBG.letter_minus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hxG hnf hnfy Φ hK hRule Y`. Rewrite `h` using `[show ((-1 : ℂ) ^ (1 - 1) * (conj τ)⁻¹) = (conj τ)⁻¹ by simp]`. Conclude with `h`.
-/
theorem first_component_of_parts : Comp1OfParts := by
  intro hNf k r j hj z z' E _ _ Dm Φ Z γ τ hH Y
  obtain ⟨hz, hz', hD, hDs, hR, hZ, hτ, hγ, hx⟩ := hH
  obtain ⟨hnf, hnfy⟩ := hNf k r j hj Z τ γ hZ hτ hγ
  have hxG : x0 k r j hj Z τ γ ∈ B.GV k r := x0_GV hj hZ hτ hγ
  have hx1 : x0 k r j hj Z τ γ ∈ Q.Glev k r 0 ∩ Dm := ⟨⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hx⟩
  have hK : Q.SmoothLev k r 0 Dm Φ := hR.1
  have hRule : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g :=
    fun g hg p q hpq => Formalism.FourierDecayAlt.P.rule_of_eq E k r z' Φ g hz' (fun n hn => (hR.2.1 g hg n hn).2) p q hpq
  refine ⟨?_, ?_⟩
  · have h := PBG.letter_plus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hnf Φ hK hRule Y
    rw [show ((-1 : ℂ) ^ (1 - 1) * τ⁻¹) = τ⁻¹ by simp] at h
    exact h
  · have h := PBG.letter_minus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hxG hnf hnfy Φ hK hRule Y
    rw [show ((-1 : ℂ) ^ (1 - 1) * (conj τ)⁻¹) = (conj τ)⁻¹ by simp] at h
    exact h

/- English proof (translation)
The claim follows from `headLetter_of_leaves normal_form_x0 leading_minors_at_base_point hL hT hSL hST hFX hFV first_component_of_parts hPP hPZ hMP hMZ`.
-/
theorem headLetter_of_open (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint) (hST : ConjugateTorusDirectionAtBasePoint)
    (hFX : FrozenX) (hFV : FrozenV) (hPP : PlusPosOfParts) (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts)
    (hMZ : MinusZeroOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of_leaves normal_form_x0 leading_minors_at_base_point hL hT hSL hST hFX hFV first_component_of_parts hPP hPZ hMP hMZ

end Formalism.FourierDecayAlt.P.CutHL
