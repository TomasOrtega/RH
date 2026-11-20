import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P n`. Set `s : Set (Ideal (MRing ι O))` to `{W | W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W}`. Set `t : Set (Ideal (MRing ι (IsLocalRing.ResidueField O)))` to `{V | V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V}`. Establish `hsupp1 : Function.support (fun W => divCycle P (C ϖ) W * n (specialIdeal W)) ⊆ s`. Introduce `W hW`.

Assume the negation of the conclusion as `h`. Apply `hW` to reduce the goal to its premises. Use `show divCycle P (C ϖ) W * n (specialIdeal W) = 0`. Establish `h' : ¬ (W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W)` using `h`. Unfold `divCycle`.

Rewrite using `[dif_neg h', zero_mul]`. Establish `hsupp2 : Function.support (fun V => idealCycle (specialIdeal P) V * n V) ⊆ t`. Introduce `V hV`. Assume the negation of the conclusion as `h`. Apply `hV` to reduce the goal to its premises.

Use `show idealCycle (specialIdeal P) V * n V = 0`. Establish `h' : ¬ (V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V)` using `h`. Unfold `idealCycle`. Rewrite using `[dif_neg h', zero_mul]`. Establish `hmem : ∀ W ∈ s, W.IsPrime ∧ (C ϖ : MRing ι O) ∈ W` using `fun W hW => ⟨hW.1.1.1, hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))⟩`.

Establish `hmaps : ∀ W ∈ s, specialIdeal W ∈ t`. Introduce `W hW`. Take `⟨hp, hc⟩` from `hmem W hW`. Take `⟨-, hmin, hrel, -⟩` from `h1 O ϖ hϖ K ι P W hp hc`. Conclude with `⟨hmin.mp hW.1, hrel.mp hW.2⟩`.

Establish `e1 : (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) = ∑ᶠ W ∈ s, divCycle P (C ϖ) W * n (specialIdeal W)`. Rewrite using `[finsum_mem_def, Set.indicator_eq_self.mpr hsupp1]`. Establish `e2 : (∑ᶠ V, idealCycle (specialIdeal P) V * n V) = ∑ᶠ V ∈ t, idealCycle (specialIdeal P) V * n V`. Rewrite using `[finsum_mem_def, Set.indicator_eq_self.mpr hsupp2]`. Use `show (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) = ∑ᶠ V, idealCycle (specialIdeal P) V * n V`.

Rewrite using `[e1, e2]`. Use `finsum_mem_eq_of_bijOn specialIdeal ⟨hmaps, ?_, ?_⟩ ?_` and prove the remaining obligations. Introduce `W hW W' hW' heq`. Take `⟨hp, hc⟩` from `hmem W hW`. Take `⟨hp', hc'⟩` from `hmem W' hW'`.

Conclude with `((h1 O ϖ hϖ K ι P W hp hc).2.2.2 W' hp' hc' heq.symm).symm`. Introduce `V hV`. Establish `hVp : V.IsPrime` using `hV.1.1.1`. Take `⟨W, hWp, hc, rfl⟩` from `h2 O ϖ hϖ K ι V hVp`. Take `⟨-, hmin, hrel, -⟩` from `h1 O ϖ hϖ K ι P W hWp hc`.

Conclude with `⟨W, ⟨hmin.mpr hV.1, hrel.mpr hV.2⟩, rfl⟩`. Introduce `W hW`. Take `⟨hp, hc⟩` from `hmem W hW`. Use `hp` as an intermediate fact. Use `(h1 O ϖ hϖ K ι P W hp hc).1` as an intermediate fact.

Establish `hm` using `h3 O ϖ hϖ K ι P W hc`. Use `congr 1`. Unfold `divCycle idealCycle`. Establish `hW' : W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W` using `hW`. Establish `hV' : specialIdeal W ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant (specialIdeal W)` using `hmaps W hW`.

Rewrite using `[dif_pos hW', dif_pos hV']`. Conclude with `congrArg (fun x : ℕ∞ => ((x.toNat : ℕ) : ℤ)) hm`.
-/
theorem SpecialCycleEval.proof (h1 : SpecialIdealCorresp.Statement.{u})
    (h2 : SpecialIdealSurj.Statement.{u}) (h3 : SpecialMultAt.Statement.{u}) :
    SpecialCycleEval.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P n
  classical
  let s : Set (Ideal (MRing ι O)) :=
    {W | W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W}
  let t : Set (Ideal (MRing ι (IsLocalRing.ResidueField O))) :=
    {V | V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V}
  have hsupp1 : Function.support (fun W => divCycle P (C ϖ) W * n (specialIdeal W)) ⊆ s := by
    intro W hW
    by_contra h
    apply hW
    show divCycle P (C ϖ) W * n (specialIdeal W) = 0
    have h' : ¬ (W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W) := h
    unfold divCycle
    rw [dif_neg h', zero_mul]
  have hsupp2 : Function.support (fun V => idealCycle (specialIdeal P) V * n V) ⊆ t := by
    intro V hV
    by_contra h
    apply hV
    show idealCycle (specialIdeal P) V * n V = 0
    have h' : ¬ (V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V) := h
    unfold idealCycle
    rw [dif_neg h', zero_mul]
  have hmem : ∀ W ∈ s, W.IsPrime ∧ (C ϖ : MRing ι O) ∈ W := fun W hW =>
    ⟨hW.1.1.1, hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))⟩
  have hmaps : ∀ W ∈ s, specialIdeal W ∈ t := by
    intro W hW
    obtain ⟨hp, hc⟩ := hmem W hW
    obtain ⟨-, hmin, hrel, -⟩ := h1 O ϖ hϖ K ι P W hp hc
    exact ⟨hmin.mp hW.1, hrel.mp hW.2⟩
  have e1 : (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) =
      ∑ᶠ W ∈ s, divCycle P (C ϖ) W * n (specialIdeal W) := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp1]
  have e2 : (∑ᶠ V, idealCycle (specialIdeal P) V * n V) =
      ∑ᶠ V ∈ t, idealCycle (specialIdeal P) V * n V := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp2]
  show (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) =
    ∑ᶠ V, idealCycle (specialIdeal P) V * n V
  rw [e1, e2]
  refine finsum_mem_eq_of_bijOn specialIdeal ⟨hmaps, ?_, ?_⟩ ?_
  · intro W hW W' hW' heq
    obtain ⟨hp, hc⟩ := hmem W hW
    obtain ⟨hp', hc'⟩ := hmem W' hW'
    exact ((h1 O ϖ hϖ K ι P W hp hc).2.2.2 W' hp' hc' heq.symm).symm
  · intro V hV
    have hVp : V.IsPrime := hV.1.1.1
    obtain ⟨W, hWp, hc, rfl⟩ := h2 O ϖ hϖ K ι V hVp
    obtain ⟨-, hmin, hrel, -⟩ := h1 O ϖ hϖ K ι P W hWp hc
    exact ⟨W, ⟨hmin.mpr hV.1, hrel.mpr hV.2⟩, rfl⟩
  · intro W hW
    obtain ⟨hp, hc⟩ := hmem W hW
    have := hp
    have := (h1 O ϖ hϖ K ι P W hp hc).1
    have hm := h3 O ϖ hϖ K ι P W hc
    congr 1
    unfold divCycle idealCycle
    have hW' : W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W := hW
    have hV' : specialIdeal W ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant (specialIdeal W) :=
      hmaps W hW
    rw [dif_pos hW', dif_pos hV']
    exact congrArg (fun x : ℕ∞ => ((x.toNat : ℕ) : ℤ)) hm

end GroundTheory.Heights₂.Heights.NumbersDVR
