import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleFiniteSupport
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

/- English proof (translation)
Unfold `divCycle`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem divCycle_nonneg (P : Ideal (MRing ι R)) (x : MRing ι R) (W : Ideal (MRing ι R)) :
    0 ≤ divCycle P x W := by
  unfold divCycle
  split_ifs <;> simp

/- English proof (translation)
Unfold `divCycle`. Rewrite using `[dif_neg]`. Conclude with `fun h => hx (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))`.
-/
theorem divCycle_eq_zero_of_form_not_mem (P : Ideal (MRing ι R)) {x : MRing ι R} {W : Ideal (MRing ι R)}
    (hx : x ∉ W) : divCycle P x W = 0 := by
  unfold divCycle
  rw [dif_neg]
  exact fun h => hx (h.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)))

end

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP ⟨G, hϖG, hsG, hDG⟩`. Establish `hPp : P.IsPrime` using `hP.multiProj.isPrime`. Establish `hGdef : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant G`. Assume the negation of the conclusion as `h`. Conclude with `hsG (by unfold divCycle; rw [dif_neg h])`.

Establish `hGp : G.IsPrime` using `hGdef.1.1.1`. Establish `hPG : P ≤ G` using `le_sup_left.trans hGdef.1.1.2`. Take `⟨u, v, huG, huv⟩` from `hD.2 G hGp hPG hGdef.2`. Establish `huP : u ∉ P` using `fun h => huG (hPG h)`. Establish `hfP` using `hD.1.num_not_mem`.

Establish `hgP` using `hD.1.den_not_mem`. Establish `hvP : v ∉ P`. Introduce `hv`. Establish `h1 : u * f ∈ P`. Establish `h2` using `P.add_mem huv (P.mul_mem_right g hv)`.

Rewrite `h2` using `[sub_add_cancel]`. Then use the resulting hypothesis. Conclude with `(hPp.mem_or_mem h1).elim huP hfP`. Establish `hcyc : divCycle P (u * f) G = divCycle P (v * g) G` using `congrFun (divCycle_congr_of_sub_mem huv) G`. Establish `huf` using `congrFun (DivCycleMul.proof O K ι P u f hPp huP hfP) G`. Establish `hvg` using `congrFun (DivCycleMul.proof O K ι P v g hPp hvP hgP) G`.

Simplify using `only [Pi.add_apply] at huf hvg`. Establish `hu0` using `divCycle_eq_zero_of_form_not_mem P huG`. Establish `hv0` using `divCycle_nonneg P v G`. Establish `hs0` using `divCycle_nonneg P s G`. Establish `hDpos : 0 < ratDiv P f g G`.

Unfold `ratDiv at hDG ⊢`. Use linear arithmetic over natural numbers and integers. Establish `hprod : 0 < (divCycle P s G * ratDiv P f g G).toNat`. Establish `: 0 < divCycle P s G * ratDiv P f g G` using `mul_pos (lt_of_le_of_ne hs0 (Ne.symm hsG)) hDpos`. Use linear arithmetic over natural numbers and integers.

Establish `hfin` using `DivCycleFiniteSupport.proof.{u} O K ι P s`. Establish `hbdd : BddAbove (Set.range fun G' : {G' : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G'} => (divCycle P s G'.1 * ratDiv P f g G'.1).toNat)`. Apply `Set.Finite.bddAbove` to reduce the goal to its premises. Apply `((hfin.image fun G' => (divCycle P s G' * ratDiv P f g G').toNat).insert 0).subset` to reduce the goal to its premises. Introduce and unpack `_ ⟨G', rfl⟩`.

Distinguish the cases in `h : divCycle P s G'.1 = 0`. Use `left`. Simplify using `[h]`. Use `right`. Conclude with `⟨G'.1, h, rfl⟩`.

Conclude with `lt_of_lt_of_le hprod (le_ciSup hbdd ⟨G, hϖG⟩)`.
-/
theorem ExcessPositive.proof : ExcessPositive.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD s hsP ⟨G, hϖG, hsG, hDG⟩
  have hPp : P.IsPrime := hP.multiProj.isPrime
  have hGdef : G ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant G := by
    by_contra h
    exact hsG (by unfold divCycle; rw [dif_neg h])
  have hGp : G.IsPrime := hGdef.1.1.1
  have hPG : P ≤ G := le_sup_left.trans hGdef.1.1.2
  obtain ⟨u, v, huG, huv⟩ := hD.2 G hGp hPG hGdef.2
  have huP : u ∉ P := fun h => huG (hPG h)
  have hfP := hD.1.num_not_mem
  have hgP := hD.1.den_not_mem
  have hvP : v ∉ P := by
    intro hv
    have h1 : u * f ∈ P := by
      have h2 := P.add_mem huv (P.mul_mem_right g hv)
      rwa [sub_add_cancel] at h2
    exact (hPp.mem_or_mem h1).elim huP hfP
  have hcyc : divCycle P (u * f) G = divCycle P (v * g) G :=
    congrFun (divCycle_congr_of_sub_mem huv) G
  have huf := congrFun (DivCycleMul.proof O K ι P u f hPp huP hfP) G
  have hvg := congrFun (DivCycleMul.proof O K ι P v g hPp hvP hgP) G
  simp only [Pi.add_apply] at huf hvg
  have hu0 := divCycle_eq_zero_of_form_not_mem P huG
  have hv0 := divCycle_nonneg P v G
  have hs0 := divCycle_nonneg P s G
  have hDpos : 0 < ratDiv P f g G := by
    unfold ratDiv at hDG ⊢
    omega
  have hprod : 0 < (divCycle P s G * ratDiv P f g G).toNat := by
    have : 0 < divCycle P s G * ratDiv P f g G := mul_pos (lt_of_le_of_ne hs0 (Ne.symm hsG)) hDpos
    omega

  have hfin := DivCycleFiniteSupport.proof.{u} O K ι P s
  have hbdd : BddAbove (Set.range fun G' : {G' : Ideal (MRing ι O) // (C ϖ : MRing ι O) ∈ G'} =>
      (divCycle P s G'.1 * ratDiv P f g G'.1).toNat) := by
    apply Set.Finite.bddAbove
    apply ((hfin.image fun G' => (divCycle P s G' * ratDiv P f g G').toNat).insert 0).subset
    rintro _ ⟨G', rfl⟩
    by_cases h : divCycle P s G'.1 = 0
    · left
      simp [h]
    · right
      exact ⟨G'.1, h, rfl⟩
  exact lt_of_lt_of_le hprod (le_ciSup hbdd ⟨G, hϖG⟩)

end GroundTheory.Heights₂.Heights.NumbersDVR
