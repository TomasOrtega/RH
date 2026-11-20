import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.BlowUpPushHypothesesExample
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

section Helpers

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem powMonomial_isMultiHomog (e : K → ℕ) (i : ∀ k, ι k) :
    IsMultiHomog (powMonomial (R := R) e i) e := by
  have h := IsWeightedHomogeneous.prod (R := R) Finset.univ (fun k => (X ⟨k, i k⟩ : MRing ι R) ^ e k)
    (fun k => e k • blockWeight ι ⟨k, i k⟩) (fun k _ => (isWeightedHomogeneous_X R _ _).pow (e k))
  have key : (∑ k, e k • blockWeight ι ⟨k, i k⟩) = e := by
    funext k'
    simp [blockWeight, Finset.sum_apply, Pi.single_apply]
  rw [key] at h
  exact h

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem liftForm_C_eq {J : Type} (a : R) : liftForm (ι := ι) (J := J) (C a : MRing ι R) = C a := by
  simp [liftForm]

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.
-/
theorem cycEval_congr_on_support {n n' : Ideal (MRing ι R) → ℤ} (Z : Ideal (MRing ι R) → ℤ)
    (h : ∀ W, Z W ≠ 0 → n W = n' W) : cycEval n Z = cycEval n' Z := by
  unfold cycEval
  refine finsum_congr fun W => ?_
  by_cases hW : Z W = 0
  · rw [hW, zero_mul, zero_mul]
  · rw [h W hW]

omit [Fintype K] [DecidableEq K] in
open Classical in

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Simplify by unfolding definitions. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem cycEval_ite (p : Ideal (MRing ι R) → Prop) (A B : Ideal (MRing ι R) → ℤ)
    (Z : Ideal (MRing ι R) → ℤ) (hZ : (Function.support Z).Finite) :
    cycEval (fun W => if p W then A W else B W) Z =
      cycEval (fun W => if p W then A W else 0) Z + cycEval (fun W => if p W then 0 else B W) Z := by
  unfold cycEval
  rw [← finsum_add_distrib (hZ.subset (Function.support_mul_subset_left _ _))
    (hZ.subset (Function.support_mul_subset_left _ _))]
  refine finsum_congr fun W => ?_
  dsimp only
  split_ifs <;> ring

omit [Fintype K] [DecidableEq K] in

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation.
-/
theorem vecCons_liftMDeg {d : ℕ} (c : K → ℕ) (L : Fin d → K → ℤ) :
    Matrix.vecCons (fun k => ((liftMDeg c k : ℕ) : ℤ)) (liftDegs L) =
      liftDegs (Matrix.vecCons (fun k => (c k : ℤ)) L) := by
  funext i o
  refine Fin.cases ?_ (fun i => ?_) i <;> cases o <;> simp [liftDegs, liftDeg, liftMDeg]

end Helpers

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. Supply the required witnesses or components. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Replace the relevant objects with their definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Establish an intermediate fact. Apply an available result and prove the equalities needed to match it to the conclusion. Reduce the equality to equality of the corresponding arguments.

Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the resulting assumption. Replace the chosen expression with an arbitrary variable.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem BlowUpInvariance.proof (hvert : BlowUpVerticalPush.Statement.{u})
    (hdiv : BlowUpDivisorPush.Statement.{u}) (hhor : BlowUpHorizontalCorresp.Statement.{u})
    (hcomp : HorizontalComponentModel.Statement.{u}) (hfin : DivCycleFiniteSupport.Statement.{u}) :
    BlowUpInvariance.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e hce m hm hmP hmH L
  obtain ⟨bf, bg, hf, hg, hb⟩ := hD.1.degrees
  have hPp := hP.multiProj.isPrime

  have hdeg : bf + e = c + bg := by
    funext k
    have h1 := hce k
    have h2 := congrFun hb k
    simp only [Pi.add_apply] at h1 h2 ⊢
    omega
  have hN : ∀ j, IsMultiHomog (blowUpGens s g f m e j) (c + bg) := by
    rintro (_ | _ | i)
    · exact hs.mul hg
    · exact hdeg ▸ hf.mul hm
    · exact hdeg ▸ hf.mul (powMonomial_isMultiHomog e i)
  have hfm : f * m ∉ P := fun h => (hPp.mem_or_mem h).elim hD.1.num_not_mem hmP
  refine ⟨?_, ?_⟩
  · unfold cutIdentityLeftSide
    rw [vecCons_liftMDeg]
    exact hdiv O ϖ hϖ K ι _ P (d + 1) hP b f g hD.1 _ _ hN ⟨some none, hfm⟩ _

  have hinv : ∀ W : Ideal (MRing ι O), W.IsPrime → P ≤ W → IsRelevant W → (C ϖ : MRing ι O) ∉ W →
      ∃ j, ∀ j', ∃ v w : MRing ι O, v ∉ W ∧
        v * blowUpGens s g f m e j' - w * blowUpGens s g f m e j ∈ P := by
    intro W hW hPW hrel hϖW
    choose i hi using hrel
    have hμ : powMonomial e i ∉ W := by
      rw [powMonomial, hW.prod_mem_iff]
      rintro ⟨k, -, hk⟩
      exact hi k (hW.mem_of_pow_mem _ hk)
    obtain ⟨u', v', hu', hv', h⟩ := hD.1.unit_off_special W hW hPW (fun k => ⟨i k, hi k⟩) hϖW
    refine ⟨some (some i), ?_⟩
    rintro (_ | _ | i')
    · refine ⟨v' * powMonomial e i, s * u', fun h' => (hW.mem_or_mem h').elim hv' hμ, ?_⟩
      have e1 : v' * powMonomial e i * (s * g) - s * u' * (f * powMonomial e i) =
          -(s * powMonomial e i) * (u' * f - v' * g) := by ring
      simpa only [blowUpGens, e1] using P.mul_mem_left _ h
    · exact ⟨powMonomial e i, m, hμ, by simp only [blowUpGens]; rw [show powMonomial e i * (f * m) -
        m * (f * powMonomial e i) = 0 by ring]; exact P.zero_mem⟩
    · exact ⟨powMonomial e i, powMonomial e i', hμ, by simp only [blowUpGens]; rw [show powMonomial e i *
        (f * powMonomial e i') - powMonomial e i' * (f * powMonomial e i) = 0 by ring]; exact P.zero_mem⟩

  obtain ⟨htrans, hpt⟩ := hhor O ϖ hϖ K ι _ P (d + 1) hP _ _ hN ⟨some none, hfm⟩ hinv c s hs hsP
  unfold cutIdentityRightSide
  rw [cycEval_ite _ _ _ _ (hfin O (Option K) (extIdx ι (BlowUpIdx ι)) (blowUpOf P (blowUpGens s g f m e))
    (liftForm s)), cycEval_ite _ _ _ _ (hfin O K ι P s)]
  congr 1
  · have hv := hvert O ϖ hϖ K ι _ P (d + 1) hP _ _ hN ⟨some none, hfm⟩ c s hs hsP (Matrix.vecCons b L)
    convert hv using 4
    congr 1
    funext i
    exact Fin.cases rfl (fun i => rfl) i
  rw [← htrans (fun W => cycEval (fun G => vNum G L) (ratDiv W f g))]
  refine cycEval_congr_on_support _ fun W hW => ?_
  by_cases hϖ' : (C ϖ : MRing (extIdx ι (BlowUpIdx ι)) O) ∈ W
  · simp only [if_pos hϖ']
  rw [if_neg hϖ', if_neg hϖ']
  obtain ⟨hWs, hWeq⟩ := hpt W hW hϖ'
  have hϖW : (C ϖ : MRing ι O) ∉ W.comap (liftForm (ι := ι) (J := BlowUpIdx ι) (R := O)) := by
    rwa [Ideal.mem_comap, liftForm_C_eq]
  generalize W.comap (liftForm (ι := ι) (J := BlowUpIdx ι) (R := O)) = V at hWs hWeq hϖW ⊢
  have hWm := hcomp O ϖ hϖ K ι P d hP c s hs hsP _ hWs hϖW
  have hWv := hsH _ hWs hϖW
  have hfmW : blowUpGens s g f m e (some none) ∉ V :=
    fun h => (hWm.multiProj.isPrime.mem_or_mem h).elim hWv.num_not_mem (hmH _ hWs hϖW)
  rw [hWeq ⟨_, hfmW⟩]
  exact hdiv O ϖ hϖ K ι _ _ d hWm b f g hWv _ _ hN ⟨_, hfmW⟩ L

end GroundTheory.Heights₂.Heights.NumbersDVR
