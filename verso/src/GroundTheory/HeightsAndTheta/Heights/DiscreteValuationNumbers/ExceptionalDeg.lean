import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.CutIdentityRightSideCongrOfSubMem
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

/- English proof (translation)
Introduce `O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L hId₁ hId₀`. Take `⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, -⟩` from `hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH`. Take `⟨hinvl, hinvr⟩` from `hinv O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L`. Use `set Q := blowUpOf P (blowUpGens s g f m e)`. Use `set Y₀ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar none`.

Use `set Y₁ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar (some none)`. Establish `hQ : Q.IsPrime` using `hmodel.multiProj.isPrime`. Establish `hfmQ` using `hE.1.num_not_mem`. Establish `hgYQ` using `hE.1.den_not_mem`. Rewrite `hfmQ` using `[map_mul]`.

Establish `hfQ : liftForm f ∉ Q` using `fun h => hfmQ (Q.mul_mem_right _ h)`. Establish `hgQ : liftForm g ∉ Q` using `fun h => hgYQ (Q.mul_mem_right _ h)`. Establish `hqQ : liftForm m * Y₁ ∉ Q` using `fun h => (hQ.mem_or_mem h).elim hD₁.1.den_not_mem hD₁.1.num_not_mem`. Establish `hcfq` using `hcf O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel (liftDeg b) (liftForm f) (liftForm g) (liftForm m * Y₁) (liftForm s) hfQ hgQ hqQ hslP (fun H hH hϖH => by`. Take `⟨h₁, h₂⟩` from `hH₁ H hH hϖH`.

Establish `hHp` using `isPrime_of_divCycle_ne_zero hH`. Use `⟨fun h => h₂.num_not_mem ?_, fun h => h₂.den_not_mem (H.mul_mem_right _ h), fun h => (hHp.mem_or_mem h).elim h₁.den_not_mem h₁.num_not_mem⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `H.mul_mem_right _ h) (liftMDeg c) (liftDegs L)`. Take `⟨haddl, haddr⟩` from `hadd O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ _ hD₁.1 hE.1 (liftMDeg c) (liftForm s) hsl hslP hH₁ (liftDegs L)`.

Establish `hnum : Y₁ * liftForm (f * m) = liftForm f * (liftForm m * Y₁)` using `by rw [map_mul]; ring`. Establish `hden : liftForm m * (liftForm g * Y₁) = liftForm g * (liftForm m * Y₁)` using `by ring`. Establish `hdeg : residualDeg e + exceptionalDeg b e = liftDeg b`. Apply the tactic sequence `funext o; cases o <;> simp [residualDeg, exceptionalDeg, liftDeg]`. Rewrite `haddl` using `[hnum, hden, hcfq.1]`.

Rewrite `haddr` using `[hnum, hden, hdeg, hcfq.2]`. Take `⟨bf, bg, hbf, hbg, hb⟩` from `hE.1.degrees`. Establish `ht` using `htaut O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf bg hbf hbg hb (liftDegs L)`. Establish `hdegs : liftMDeg c + bg = bf + Pi.single none 1`. Use function extensionality and compare the values at `o`.

Establish `h` using `congrFun hb o`. Consider the cases of `o with`. Consider the case `none => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢`. Use linear arithmetic over natural numbers and integers. Consider the case `some k => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢`.

Use `he k` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hl₁` using `hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 (liftMDeg c) bg (liftDegs L)`. Establish `hl₂` using `hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf (Pi.single none 1) (liftDegs L)`. Rewrite `hl₁` using `[hdegs]`.

Establish `hrel` using `cutIdentityRightSide_congr_of_sub_mem ϖ Q (exceptionalDeg b e) (liftForm (f * m)) (liftForm g * Y₁) (blowUp_relation P s g f m e) (liftDegs L)`. Establish `hsg : liftForm (s * g) * Y₁ = liftForm s * (liftForm g * Y₁)` using `by rw [map_mul]; ring`. Rewrite `hrel` using `[hsg, hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hslP hE.1.den_not_mem, hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hE.1.num_not_mem hY₀P]`. Rewrite `hId₁`, `hId₀`, the goal using `[cutIdentity_iff]`. Rewrite using `[← hinvl, ← hinvr]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem BlowUpReduction.proof (hpieces : BlowUpDecomposition.Statement.{u})
    (hinv : BlowUpInvariance.Statement.{u}) (hcf : CommonFactorRemoval.Statement.{u})
    (hadd : AdditivityInDivisor.Statement.{u}) (hrhs : RightSideMultiplicativeInForm.Statement.{u})
    (hlhs : LeftSideAdditiveInDegree.Statement.{u}) (htaut : TautologicalCase.Statement.{u}) :
    BlowUpReduction.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L hId₁ hId₀
  obtain ⟨hmodel, hsl, hslP, hY₀P, hD₁, hE, hH₁, -⟩ :=
    hpieces O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH
  obtain ⟨hinvl, hinvr⟩ := hinv O ϖ hϖ K ι P d hP b f g hD c s hs hsP hsH e he m hm hmP hmH L
  set Q := blowUpOf P (blowUpGens s g f m e)
  set Y₀ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar none
  set Y₁ : MRing (extIdx ι (BlowUpIdx ι)) O := newVar (some none)
  have hQ : Q.IsPrime := hmodel.multiProj.isPrime
  have hfmQ := hE.1.num_not_mem
  have hgYQ := hE.1.den_not_mem
  rw [map_mul] at hfmQ
  have hfQ : liftForm f ∉ Q := fun h => hfmQ (Q.mul_mem_right _ h)
  have hgQ : liftForm g ∉ Q := fun h => hgYQ (Q.mul_mem_right _ h)
  have hqQ : liftForm m * Y₁ ∉ Q := fun h =>
    (hQ.mem_or_mem h).elim hD₁.1.den_not_mem hD₁.1.num_not_mem

  have hcfq := hcf O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel (liftDeg b) (liftForm f)
    (liftForm g) (liftForm m * Y₁) (liftForm s) hfQ hgQ hqQ hslP (fun H hH hϖH => by
      obtain ⟨h₁, h₂⟩ := hH₁ H hH hϖH
      have hHp := isPrime_of_divCycle_ne_zero hH
      refine ⟨fun h => h₂.num_not_mem ?_, fun h => h₂.den_not_mem (H.mul_mem_right _ h),
        fun h => (hHp.mem_or_mem h).elim h₁.den_not_mem h₁.num_not_mem⟩
      rw [map_mul]; exact H.mul_mem_right _ h) (liftMDeg c) (liftDegs L)
  obtain ⟨haddl, haddr⟩ := hadd O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ _
    hD₁.1 hE.1 (liftMDeg c) (liftForm s) hsl hslP hH₁ (liftDegs L)
  have hnum : Y₁ * liftForm (f * m) = liftForm f * (liftForm m * Y₁) := by rw [map_mul]; ring
  have hden : liftForm m * (liftForm g * Y₁) = liftForm g * (liftForm m * Y₁) := by ring
  have hdeg : residualDeg e + exceptionalDeg b e = liftDeg b := by
    funext o; cases o <;> simp [residualDeg, exceptionalDeg, liftDeg]
  rw [hnum, hden, hcfq.1] at haddl
  rw [hnum, hden, hdeg, hcfq.2] at haddr

  obtain ⟨bf, bg, hbf, hbg, hb⟩ := hE.1.degrees
  have ht := htaut O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf bg hbf hbg hb
    (liftDegs L)
  have hdegs : liftMDeg c + bg = bf + Pi.single none 1 := by
    funext o
    have h := congrFun hb o
    cases o with
    | none => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; omega
    | some k => simp [exceptionalDeg, liftDeg, liftMDeg] at h ⊢; have := he k; omega
  have hl₁ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 (liftMDeg c) bg
    (liftDegs L)
  have hl₂ := hlhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ hE.1 bf
    (Pi.single none 1) (liftDegs L)
  rw [hdegs] at hl₁
  have hrel := cutIdentityRightSide_congr_of_sub_mem ϖ Q (exceptionalDeg b e) (liftForm (f * m))
    (liftForm g * Y₁) (blowUp_relation P s g f m e) (liftDegs L)
  have hsg : liftForm (s * g) * Y₁ = liftForm s * (liftForm g * Y₁) := by rw [map_mul]; ring
  rw [hsg, hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hslP hE.1.den_not_mem,
    hrhs O ϖ hϖ (Option K) (extIdx ι (BlowUpIdx ι)) Q d hmodel _ _ _ _ _ hE.1.num_not_mem hY₀P] at hrel
  rw [cutIdentity_iff] at hId₁ hId₀ ⊢
  rw [← hinvl, ← hinvr]
  linarith

end GroundTheory.Heights₂.Heights.NumbersDVR
