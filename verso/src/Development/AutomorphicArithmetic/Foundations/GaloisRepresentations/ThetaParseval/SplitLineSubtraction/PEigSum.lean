import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

/- English proof (translation)
Simplify using `[dg, Matrix.mulVec_diagonal]`.
-/
private theorem dg_mulVec {Γ k : Type} [Group Γ] [Field k] {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ)
    (u : Fin t → k) (i : Fin t) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).mulVec u i = (a i g : k) * u i := by
  simp [dg, Matrix.mulVec_diagonal]

/- English proof (translation)
Introduce `Γ k _ _ m t r a c`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨i, hi⟩`. Set `e : Fin t → k` to `Pi.single i 1`. Set `w : Fin (m + t) → k` to `fun x => (finSumFinEquiv.symm x).elim (fun _ => 0) e`.

Establish `hwl : w ∘ ⇑finSumFinEquiv ∘ Sum.inl = 0`. Use function extensionality and compare the values at `y`. Simplify using `[w]`. Establish `hwr : w ∘ ⇑finSumFinEquiv ∘ Sum.inr = e`. Use function extensionality and compare the values at `y`.

Simplify using `[w]`. Use `⟨w, ?_, ?_⟩` and prove the remaining obligations. Introduce `h`. Use `congrFun hwr i` as an intermediate fact. Rewrite `this` using `[h]`.

Simplify using `[e] at this`. Introduce `g`. Use function extensionality and compare the values at `x`. Take `⟨y, rfl⟩` from `finSumFinEquiv.surjective x`. Break down `y with y | y` into its components or cases.

Rewrite using `[GlobalTheory.EigTwist.sumRep_mulVec_inl, hwl, Matrix.mulVec_zero, Pi.smul_apply]`. Use `congrFun hwl y` as an intermediate fact. Simplify using `only [Function.comp_apply] at this`. Rewrite using `[this]`. Simplify using the standard rewrite rules.

Rewrite using `[GlobalTheory.EigTwist.sumRep_mulVec_inr, hwr, dg_mulVec]`. Use `congrFun hwr y` as an intermediate fact. Simplify using `only [Function.comp_apply] at this`. Rewrite using `[Pi.smul_apply, this, smul_eq_mul]`. Distinguish the cases in `hy : y = i`.

Substitute `hy` using the available equality. Rewrite using `[hi]`. Simplify using `[e, Pi.single_apply, hy]`. Introduce `hne hex`. Take `⟨w, hw0, hw⟩` from `hex`.

Break down `GlobalTheory.EigTwist.eigen_pair c r (dg a) w hw0 hw with h | ⟨v, hv0, hv⟩` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, v j ≠ 0 := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hv0 (funext hcon)`. Apply `hne j` to reduce the goal to its premises. Use extensionality with `g`. Use `congrFun (hv g) j` as an intermediate fact.

Rewrite `this` using `[dg_mulVec, Pi.smul_apply, smul_eq_mul]`. Conclude with `mul_right_cancel₀ hj this`.
-/
theorem UpperTheory.Gal.TP.Sub.eigSum_holds :
    EigSum := by
  intro Γ k _ _ m t r a c
  refine ⟨?_, ?_⟩
  · rintro ⟨i, hi⟩
    let e : Fin t → k := Pi.single i 1
    let w : Fin (m + t) → k := fun x => (finSumFinEquiv.symm x).elim (fun _ => 0) e
    have hwl : w ∘ ⇑finSumFinEquiv ∘ Sum.inl = 0 := by
      funext y
      simp [w]
    have hwr : w ∘ ⇑finSumFinEquiv ∘ Sum.inr = e := by
      funext y
      simp [w]
    refine ⟨w, ?_, ?_⟩
    · intro h
      have := congrFun hwr i
      rw [h] at this
      simp [e] at this
    · intro g
      funext x
      obtain ⟨y, rfl⟩ := finSumFinEquiv.surjective x
      rcases y with y | y
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inl, hwl, Matrix.mulVec_zero, Pi.smul_apply]
        have := congrFun hwl y
        simp only [Function.comp_apply] at this
        rw [this]
        simp
      · rw [GlobalTheory.EigTwist.sumRep_mulVec_inr, hwr, dg_mulVec]
        have := congrFun hwr y
        simp only [Function.comp_apply] at this
        rw [Pi.smul_apply, this, smul_eq_mul]
        by_cases hy : y = i
        · subst hy
          rw [hi]
        · simp [e, Pi.single_apply, hy]
  · intro hne hex
    obtain ⟨w, hw0, hw⟩ := hex
    rcases GlobalTheory.EigTwist.eigen_pair c r (dg a) w hw0 hw with h | ⟨v, hv0, hv⟩
    · exact h
    · exfalso
      obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hv0 (funext hcon)
      apply hne j
      ext g
      have := congrFun (hv g) j
      rw [dg_mulVec, Pi.smul_apply, smul_eq_mul] at this
      exact mul_right_cancel₀ hj this
