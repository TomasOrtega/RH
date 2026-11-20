import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTail
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'`. Use `set P' := blowUpOf P (blowUpGens s g f m e) with hP'def`. Establish `hPprime : P.IsPrime` using `hP.multiProj.isPrime`. Establish `hP'prime : P'.IsPrime` using `RingHom.ker_isPrime _`. Establish `hmul` using `DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'`.

Establish `hlm : liftForm (J` using `BlowUpIdx ι) m ∉ P' := fun h => by`. Rewrite `h` using `[hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hmP h`. Establish `hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P'` using `fun h => by`. Rewrite `h` using `[hP'def, blowUpOf, RingHom.mem_ker]`.

Simplify using `only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false, Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h`. Conclude with `(hPprime.mem_or_mem h).elim hD.1.num_not_mem hmP`. Establish `hnonneg : ∀ x W, 0 ≤ divCycle P' x W` using `fun x W => by`. Apply the tactic sequence `unfold divCycle; split_ifs <;> simp`. Establish `hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0` using `fun x hx => by`.

Assume the negation of the conclusion as `h`. Conclude with `hx (form_mem_of_divCycle_ne_zero h)`. Establish `hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G'`. Assume the negation of the conclusion as `h`. Unfold `divCycle at hsG'`.

Rewrite `hsG'` using `[dif_neg h]`. Conclude with `lt_irrefl _ hsG'`. Establish `hP'G' : P' ≤ G'` using `le_sup_left.trans hG'supp.1.1.2`. Establish `hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G'`. Apply `form_mem_of_divCycle_ne_zero (P := P')` to reduce the goal to its premises.

Use `hnonneg (liftForm m) G'` as an intermediate fact. Unfold `ratDiv at hresG'`. Use linear arithmetic over natural numbers and integers. Establish `hYiG' : ∀ i : ∀ k, ι k, (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G'`. Introduce `i`.

Assume the negation of the conclusion as `hYi`. Establish `hrel : liftForm (powMonomial e i) * newVar (some none) - liftForm m * newVar (some (some i)) ∈ P'`. Rewrite using `[hP'def, blowUpOf, RingHom.mem_ker]`. Simplify using `only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P'` using `fun h => hYi (hP'G' h)`. Distinguish the cases in `hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι O) ∈ P'`. Establish `h` using `P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel`. Rewrite `h` using `[sub_sub_cancel]`. Conclude with `(hP'prime.mem_or_mem h).elim hlm hYiP'`.

Establish `h1` using `congrFun (divCycle_congr_of_sub_mem hrel) G'`. Rewrite `h1` using `[hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP']`. Simplify using `only [Pi.add_apply] at h1`. Establish `h2` using `hzero _ hYi`. Establish `h3` using `hnonneg (liftForm (powMonomial e i)) G'`.

Unfold `ratDiv at hresG'`. Use linear arithmetic over natural numbers and integers. Take `⟨j, hj⟩` from `hG'supp.2 none`. Express the relevant statement in the definitionally equal form `BlowUpIdx ι at j`. Break down `j with _ | _ | i` into its components or cases.

Conclude with `hj`. Conclude with `absurd hY₁G' hj`. Conclude with `absurd (hYiG' i) hj`.
-/
theorem ResidualDisjoint.proof : ResidualDisjoint.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH G' hϖG' hsG' hresG'
  set P' := blowUpOf P (blowUpGens s g f m e) with hP'def
  have hPprime : P.IsPrime := hP.multiProj.isPrime
  have hP'prime : P'.IsPrime := RingHom.ker_isPrime _
  have hmul := DivCycleMul.proof O (Option K) (extIdx ι (BlowUpIdx ι)) P'
  have hlm : liftForm (J := BlowUpIdx ι) m ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker, aeval_blowUpSubst_liftForm, Polynomial.C_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem] at h
    exact hmP h
  have hY₁P' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => by
    rw [hP'def, blowUpOf, RingHom.mem_ker] at h
    simp only [newVar, aeval_X, blowUpSubst, blowUpGens, mul_eq_zero, Polynomial.X_ne_zero, or_false,
      Polynomial.C_eq_zero, Ideal.Quotient.eq_zero_iff_mem] at h
    exact (hPprime.mem_or_mem h).elim hD.1.num_not_mem hmP
  have hnonneg : ∀ x W, 0 ≤ divCycle P' x W := fun x W => by
    unfold divCycle; split_ifs <;> simp
  have hzero : ∀ x, x ∉ G' → divCycle P' x G' = 0 := fun x hx => by
    by_contra h; exact hx (form_mem_of_divCycle_ne_zero h)
  have hG'supp : G' ∈ (P' ⊔ Ideal.span {liftForm s}).minimalPrimes ∧ IsRelevant G' := by
    by_contra h; unfold divCycle at hsG'; rw [dif_neg h] at hsG'; exact lt_irrefl _ hsG'
  have hP'G' : P' ≤ G' := le_sup_left.trans hG'supp.1.1.2

  have hY₁G' : (newVar (some none) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' := by
    apply form_mem_of_divCycle_ne_zero (P := P')
    have := hnonneg (liftForm m) G'
    unfold ratDiv at hresG'; omega

  have hYiG' : ∀ i : ∀ k, ι k, (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ G' := by
    intro i
    by_contra hYi
    have hrel : liftForm (powMonomial e i) * newVar (some none) -
        liftForm m * newVar (some (some i)) ∈ P' := by
      rw [hP'def, blowUpOf, RingHom.mem_ker]
      simp only [map_sub, map_mul, aeval_blowUpSubst_liftForm, newVar, aeval_X, blowUpSubst, blowUpGens]
      ring
    have hYiP' : (newVar (some (some i)) : MRing (extIdx ι (BlowUpIdx ι)) O) ∉ P' := fun h => hYi (hP'G' h)
    by_cases hp : liftForm (J := BlowUpIdx ι) (powMonomial e i : MRing ι O) ∈ P'
    · have h := P'.sub_mem (P'.mul_mem_right (newVar (some none)) hp) hrel
      rw [sub_sub_cancel] at h
      exact (hP'prime.mem_or_mem h).elim hlm hYiP'
    · have h1 := congrFun (divCycle_congr_of_sub_mem hrel) G'
      rw [hmul _ _ hP'prime hp hY₁P', hmul _ _ hP'prime hlm hYiP'] at h1
      simp only [Pi.add_apply] at h1
      have h2 := hzero _ hYi
      have h3 := hnonneg (liftForm (powMonomial e i)) G'
      unfold ratDiv at hresG'; omega

  obtain ⟨j, hj⟩ := hG'supp.2 none
  change BlowUpIdx ι at j
  rcases j with _ | _ | i
  · exact hj
  · exact absurd hY₁G' hj
  · exact absurd (hYiG' i) hj

end GroundTheory.Heights₂.Heights.NumbersDVR
