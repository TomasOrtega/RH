import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.MeasurableSetUH
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ExistsEqAdelicCharMul

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.GFac

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open PositivityTheory.SiegelWeilFormula.Gen
open GlobalTheory.CompanionTheory.SiegelND.Coef (hermInf hermFin hermV latH intH)
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evalV_apply (v : HeightOneSpectrum (𝓞 F)) (a : Af F) : evalV F v a = a v := rfl

open Classical in
/- English proof (translation)
Rewrite using `[evalV_apply]`. Unfold `singleV`. Conclude with `RestrictedProduct.single_eq_same _ _ _`.
-/
theorem evalV_singleV_same (v : HeightOneSpectrum (𝓞 F)) (y : Fv F v) : evalV F v (singleV F v y) = y := by
  rw [evalV_apply]
  unfold singleV
  exact RestrictedProduct.single_eq_same _ _ _

open Classical in
/- English proof (translation)
Rewrite using `[evalV_apply]`. Unfold `singleV`. Conclude with `RestrictedProduct.single_eq_of_ne _ _ h`.
-/
theorem evalV_singleV_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) (y : Fv F v) : evalV F w (singleV F v y) = 0 := by
  rw [evalV_apply]
  unfold singleV
  exact RestrictedProduct.single_eq_of_ne _ _ h

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]`.
-/
theorem addChar_sum {A M ι : Type} [AddCommMonoid A] [CommMonoid M] (ψ : AddChar A M) (s : Finset ι) (f : ι → A) :
    ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]

/- English proof (translation)
The claim follows from `Prod.ext (α := Ainf F) (β := Af F) h1 h2`.
-/
theorem AF_ext {a b : AF F} (h1 : fstA F a = fstA F b) (h2 : sndA F a = sndA F b) : a = b :=
  Prod.ext (α := Ainf F) (β := Af F) h1 h2

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem fstA_pairA (x : Ainf F) (y : Af F) : fstA F (pairA F x y) = x := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sndA_pairA (x : Ainf F) (y : Af F) : sndA F (pairA F x y) = y := rfl

/- English proof (translation)
Take `⟨ξ, hξ⟩` from `GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F}.Finite` using `Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat ξ)`. Use `⟨hfin.toFinset, fun S hS x hx => ?_⟩` and prove the remaining obligations. Use `set xf : Af F := sndA F x with hxf`. Use `set r : Af F := xf - ∑ v ∈ S, singleV F v (evalV F v xf) with hr`.

Establish `hdec : x = pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r`. Use `AF_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[map_add, map_add, map_sum, fstA_pairA, fstA_pairA]`. Simplify using `only [fstA_pairA, Finset.sum_const_zero, add_zero]`. Rewrite using `[map_add, map_add, map_sum, sndA_pairA, sndA_pairA]`.

Simplify using `only [sndA_pairA, hr, hxf]`. Normalize the expressions using the abelian group laws. Establish `hrv : ∀ v, evalV F v r = if v ∈ S then 0 else evalV F v xf`. Introduce `v`. Rewrite using `[hr, map_sub, map_sum]`.

Distinguish the cases in `hv : v ∈ S`. Rewrite using `[if_pos hv, Finset.sum_eq_single v]`. Rewrite using `[evalV_singleV_same, sub_self]`. Introduce `w _ hw`. Conclude with `evalV_singleV_ne (Ne.symm hw) _`.

Introduce `h`. Conclude with `absurd hv h`. Rewrite using `[if_neg hv, Finset.sum_eq_zero, sub_zero]`. Introduce `w hw`. Conclude with `evalV_singleV_ne (by rintro rfl; exact hv hw) _`.

Establish `hmem : algebraMap F (Af F) ξ * r ∈ GroundTheory.Global.finiteInvDifferent F`. Introduce `v`. Establish `e1 : (algebraMap F (Af F) ξ * r) v = algebraMap F (Fv F v) ξ * evalV F v r` using `rfl`. Rewrite using `[e1, hrv v]`. Distinguish the cases in `hv : v ∈ S`.

Rewrite using `[if_pos hv, mul_zero]`. Conclude with `zero_mem _`. Rewrite using `[if_neg hv]`. Establish `hξv : algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F`. Assume the negation of the conclusion as `h`.

Conclude with `hv (hS (hfin.mem_toFinset.2 h))`. Conclude with `GroundTheory.Global.mem_localInvDifferent_of_mem (mul_mem hξv (hx v hv))`. Establish `hr1 : ψ (pairA F 0 r) = 1`. Rewrite using `[hξ]`. Establish `e2 : algebraMap F (AF F) ξ * pairA F 0 r = pairA F 0 (algebraMap F (Af F) ξ * r)`.

Use `AF_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, fstA_pairA, fstA_pairA, mul_zero]`. Rewrite using `[map_mul, sndA_pairA, sndA_pairA, AlgHom.commutes]`. Rewrite using `[e2]`. Establish `hm2 : pairA F 0 (algebraMap F (Af F) ξ * r) ∈ GroundTheory.Global.invDifferentAdeles F` using `GroundTheory.Global.mem_invDifferentAdeles.mpr hmem`.

Rewrite using `[GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hm2]`. Simplify using `[pairA]`. Establish `h1 : ψ x = ψ (pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r)` using `congrArg ψ hdec`. Rewrite using `[h1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, addChar_sum, hr1, mul_one]`. Both sides reduce to the same expression.
-/
theorem psi_split (ψ : AddChar (AF F) ℂ) (hψ : IsCharAF F ψ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S → ∀ x : AF F,
      (∀ v, v ∉ S → evalV F v (sndA F x) ∈ v.adicCompletionIntegers F) →
      ψ x = psiInf F ψ (fstA F x) * ∏ v ∈ S, psiV F ψ v (evalV F v (sndA F x)) := by
  classical
  obtain ⟨ξ, hξ⟩ := GlobalTheory.CompanionTheory.AdeleDual.exists_eq_adelicChar_mul ψ hψ.1 hψ.2.2.1
  have hfin : {v : HeightOneSpectrum (𝓞 F) | ¬ algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 (GlobalTheory.CompanionTheory.SiegelND.Coef.Lim.ev_rat ξ)
  refine ⟨hfin.toFinset, fun S hS x hx => ?_⟩
  set xf : Af F := sndA F x with hxf
  set r : Af F := xf - ∑ v ∈ S, singleV F v (evalV F v xf) with hr
  have hdec : x = pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r := by
    refine AF_ext ?_ ?_
    · rw [map_add, map_add, map_sum, fstA_pairA, fstA_pairA]
      simp only [fstA_pairA, Finset.sum_const_zero, add_zero]
    · rw [map_add, map_add, map_sum, sndA_pairA, sndA_pairA]
      simp only [sndA_pairA, hr, hxf]
      abel
  have hrv : ∀ v, evalV F v r = if v ∈ S then 0 else evalV F v xf := by
    intro v
    rw [hr, map_sub, map_sum]
    by_cases hv : v ∈ S
    · rw [if_pos hv, Finset.sum_eq_single v]
      · rw [evalV_singleV_same, sub_self]
      · intro w _ hw
        exact evalV_singleV_ne (Ne.symm hw) _
      · intro h; exact absurd hv h
    · rw [if_neg hv, Finset.sum_eq_zero, sub_zero]
      intro w hw
      exact evalV_singleV_ne (by rintro rfl; exact hv hw) _
  have hmem : algebraMap F (Af F) ξ * r ∈ GroundTheory.Global.finiteInvDifferent F := by
    intro v
    have e1 : (algebraMap F (Af F) ξ * r) v = algebraMap F (Fv F v) ξ * evalV F v r := rfl
    rw [e1, hrv v]
    by_cases hv : v ∈ S
    · rw [if_pos hv, mul_zero]
      exact zero_mem _
    · rw [if_neg hv]
      have hξv : algebraMap F (Fv F v) ξ ∈ v.adicCompletionIntegers F := by
        by_contra h
        exact hv (hS (hfin.mem_toFinset.2 h))
      exact GroundTheory.Global.mem_localInvDifferent_of_mem (mul_mem hξv (hx v hv))
  have hr1 : ψ (pairA F 0 r) = 1 := by
    rw [hξ]
    have e2 : algebraMap F (AF F) ξ * pairA F 0 r = pairA F 0 (algebraMap F (Af F) ξ * r) := by
      refine AF_ext ?_ ?_
      · rw [map_mul, fstA_pairA, fstA_pairA, mul_zero]
      · rw [map_mul, sndA_pairA, sndA_pairA, AlgHom.commutes]
    rw [e2]
    have hm2 : pairA F 0 (algebraMap F (Af F) ξ * r) ∈ GroundTheory.Global.invDifferentAdeles F :=
      GroundTheory.Global.mem_invDifferentAdeles.mpr hmem
    rw [GroundTheory.Global.adelicChar_of_mem_invDifferentAdeles hm2]
    simp [pairA]
  have h1 : ψ x = ψ (pairA F (fstA F x) 0 + ∑ v ∈ S, pairA F 0 (singleV F v (evalV F v xf)) + pairA F 0 r) :=
    congrArg ψ hdec
  rw [h1, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul, addChar_sum, hr1, mul_one]
  rfl

end PositivityTheory.SiegelWeilFormula.GFac

end
