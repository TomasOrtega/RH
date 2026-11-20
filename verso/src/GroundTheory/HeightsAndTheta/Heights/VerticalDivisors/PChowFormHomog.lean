import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.ChowFormHomog
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

variable {F : Type} [Field F] {n k : ℕ}

/- English proof (translation)
Take `⟨q, rfl⟩ : f ∣ g` from `(hf.2 g).mp ((hg.2 g).mpr dvd_rfl)`. Take `⟨r, hr⟩ : f * q ∣ f` from `(hg.2 f).mp ((hf.2 f).mpr dvd_rfl)`. Establish `hqr : q * r = 1`. Establish `h' : f * (q * r) = f * 1`. Rewrite using `[mul_one, ← mul_assoc]`.

Conclude with `hr.symm`. Conclude with `mul_left_cancel₀ hf.1 h'`. Take `⟨c, -, rfl⟩` from `(isUnit_iff_eq_C_of_isReduced (P := q)).mp (IsUnit.of_mul_eq_one r hqr)`. Establish `h1 : IsWeightedHomogeneous (groupWeight k n) (f * C c) ((fun _ => δ) + 0)` using `IsWeightedHomogeneous.mul hδ (isWeightedHomogeneous_C _ c)`. Rewrite `h1` using `[add_zero]`.

Conclude with `congrFun (IsWeightedHomogeneous.inj_right hg.1 h1 hδ') ⟨0, hk⟩`.
-/
theorem chowForm_degree_unique {I : Ideal (MvPolynomial (Fin n) F)}
    {f g : MvPolynomial (Fin k × Fin n) F} (hk : 0 < k) (hf : IsChowForm I k f)
    (hg : IsChowForm I k g) {δ δ' : ℕ} (hδ : IsMultiHomog δ f) (hδ' : IsMultiHomog δ' g) :
    δ = δ' := by
  obtain ⟨q, rfl⟩ : f ∣ g := (hf.2 g).mp ((hg.2 g).mpr dvd_rfl)
  obtain ⟨r, hr⟩ : f * q ∣ f := (hg.2 f).mp ((hf.2 f).mpr dvd_rfl)
  have hqr : q * r = 1 := by
    have h' : f * (q * r) = f * 1 := by
      rw [mul_one, ← mul_assoc]
      exact hr.symm
    exact mul_left_cancel₀ hf.1 h'
  obtain ⟨c, -, rfl⟩ := (isUnit_iff_eq_C_of_isReduced (P := q)).mp (IsUnit.of_mul_eq_one r hqr)
  have h1 : IsWeightedHomogeneous (groupWeight k n) (f * C c) ((fun _ => δ) + 0) :=
    IsWeightedHomogeneous.mul hδ (isWeightedHomogeneous_C _ c)
  rw [add_zero] at h1
  exact congrFun (IsWeightedHomogeneous.inj_right hg.1 h1 hδ') ⟨0, hk⟩

/- English proof (translation)
Introduce `F _ n k I f hf`. Break down `Nat.eq_zero_or_pos k with hk0 | hk` into its components or cases. Substitute `hk0` using the available equality. Conclude with `fun d _ => funext fun i => i.elim0`. Use `choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i`.

Establish `hδ : IsMultiHomog (a ⟨0, hk⟩) f` using `(isMultiHomog_iff _ _).mpr fun i => by`. Rewrite using `[hf.degrees_eq ha ⟨0, hk⟩ i]`. Conclude with `ha i`. Establish `hdeg : chowDegree I k = a ⟨0, hk⟩`. Apply `le_antisymm` to reduce the goal to its premises.

Conclude with `Nat.sInf_le ⟨f, hf, hδ⟩`. Conclude with `le_csInf ⟨_, f, hf, hδ⟩ fun δ ⟨g, hg, hδg⟩ => (chowForm_degree_unique hk hf hg hδ hδg).le`. Rewrite using `[hdeg]`. Conclude with `hδ`.
-/
theorem ChowFormHomog.proof : ChowFormHomog.Statement := by
  intro F _ n k I f hf
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    exact fun d _ => funext fun i => i.elim0
  choose a ha using fun i => hf.exists_isWeightedHomogeneous_inGroup i
  have hδ : IsMultiHomog (a ⟨0, hk⟩) f := (isMultiHomog_iff _ _).mpr fun i => by
    rw [hf.degrees_eq ha ⟨0, hk⟩ i]
    exact ha i
  have hdeg : chowDegree I k = a ⟨0, hk⟩ := by
    apply le_antisymm
    · exact Nat.sInf_le ⟨f, hf, hδ⟩
    · exact le_csInf ⟨_, f, hf, hδ⟩ fun δ ⟨g, hg, hδg⟩ =>
        (chowForm_degree_unique hk hf hg hδ hδg).le
  rw [hdeg]
  exact hδ

/- English proof (translation)
The claim follows from `ChowFormHomog.proof`.
-/
theorem chowFormHomog : ChowFormHomog.Statement := ChowFormHomog.proof

/- English proof (translation)
The claim follows from `ChowFormHomog.proof ℚ 1 1 ⊥ _ (isChowForm_point ℚ)`.
-/
example : IsMultiHomog (chowDegree (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) 1)
    (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℚ) :=
  ChowFormHomog.proof ℚ 1 1 ⊥ _ (isChowForm_point ℚ)

end GroundTheory.Heights₂.Heights.Vertical
