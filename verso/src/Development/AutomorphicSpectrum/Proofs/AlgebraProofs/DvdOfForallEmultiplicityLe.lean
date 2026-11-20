import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionPerfect
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowFormSectionAlgClosed
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionCycleReduced
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMinimalPrimeComap
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsFundCycleBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PRadicalBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExtend
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormBaseChange
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormAssoc
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleAdd
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormCycleSmul
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealSeparate
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncidenceZeroLocus
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PFormsThroughPoint
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughPointIncIdeal
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartZeroTrdeg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PThroughTwoPointsTrdeg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegAdjoinLe
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PTrdegBaseAlgebraic
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PIncIdealNeBotDim
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LocalMultRadical
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PFGNullstellensatz
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncidenceGeneric
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealPrime
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PGenericLinearTrdeg
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormExists
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimComponent
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormReducedRadical
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionOrderAlgClosed
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionComponents
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsSectionLengthSum

set_option maxSynthPendingDepth 1

namespace GlobalTheory.CompanionTheory.Ar.Short.ChowClosing

open MvPolynomial GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.ObjectsChow

/- English proof (translation)
Rewrite using `[Finsupp.mem_support_iff]`. Unfold `fundCycle`. Rewrite using `[Finsupp.onFinset_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `h'`. Conclude with `h (if_neg h')`. Introduce `h`. Rewrite using `[if_pos h, localMult_eq_one_of_isRadical hJ h.1]`. Conclude with `one_ne_zero`.
-/
theorem mem_support_fundCycle_iff {F : Type*} [Field F] {n : ℕ} {J : Ideal (MvPolynomial (Fin n) F)} (hJ : J.IsRadical)
    {W : Ideal (MvPolynomial (Fin n) F)} : W ∈ (fundCycle J).support ↔ W ∈ relComps J := by
  classical
  rw [Finsupp.mem_support_iff]
  unfold fundCycle
  rw [Finsupp.onFinset_apply]
  constructor
  · intro h
    by_contra h'
    exact h (if_neg h')
  · intro h
    rw [if_pos h, localMult_eq_one_of_isRadical hJ h.1]
    exact one_ne_zero

namespace SectionPerfect

/- English proof (translation)
The claim follows from `IncIdealPrime.proof (IncidenceGeneric.proof FGNullstellensatz.proof)`.
-/
theorem incIdealPrime_full : IncIdealPrime.Statement :=
  IncIdealPrime.proof (IncidenceGeneric.proof FGNullstellensatz.proof)

/- English proof (translation)
The claim follows from `IncIdealDim.proof (IncidenceGeneric.proof FGNullstellensatz.proof) GenericLinearTrdeg.proof AffineChartTrdeg.proof`.
-/
theorem incIdealDim_full : IncIdealDim.Statement :=
  IncIdealDim.proof (IncidenceGeneric.proof FGNullstellensatz.proof) GenericLinearTrdeg.proof
    AffineChartTrdeg.proof

/- English proof (translation)
The claim follows from `ChowFormExists.proof incIdealDim_full incIdealPrime_full`.
-/
theorem chowFormExists_full : ChowFormExists.Statement :=
  ChowFormExists.proof incIdealDim_full incIdealPrime_full

/- English proof (translation)
The claim follows from `ChowFormReduced.proof_of_prime_separate incIdealPrime_full (IncIdealSeparate.proof IncidenceZeroLocus.proof (FormsThroughPoint.proof IncidenceZeroLocus.proof ThroughPointIncIdeal.proof (ChartZeroTrdeg.proof AffineChartTrdeg.proof) (ThroughTwoPointsTrdeg.proof TrdegAdjoinLe.proof) …`.
-/
theorem chowFormReduced_full : ChowFormReduced.Statement :=
  ChowFormReduced.proof_of_prime_separate incIdealPrime_full
    (IncIdealSeparate.proof IncidenceZeroLocus.proof
      (FormsThroughPoint.proof IncidenceZeroLocus.proof ThroughPointIncIdeal.proof
        (ChartZeroTrdeg.proof AffineChartTrdeg.proof) (ThroughTwoPointsTrdeg.proof TrdegAdjoinLe.proof)
        TrdegBaseAlgebraic.proof)
      (IncIdealNeBotDim.proof incIdealDim_full))

/- English proof (translation)
The claim follows from `ChowFormExtend.proof RadicalBaseChange.proof`.
-/
theorem chowFormExtend_full : ChowFormExtend.Statement :=
  ChowFormExtend.proof RadicalBaseChange.proof

/- English proof (translation)
The claim follows from `ConeDimOfChowForm.proof incIdealDim_full incIdealPrime_full`.
-/
theorem coneDimOfChowForm_full : ConeDimOfChowForm.Statement :=
  ConeDimOfChowForm.proof incIdealDim_full incIdealPrime_full

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, one_ne_zero, fun _ => 1, by simp, by simp⟩`.
-/
theorem isChowFormCycle_zero (F : Type) [Field F] (n k : ℕ) :
    IsChowFormCycle (0 : ProjCycle F n) k 1 :=
  ⟨1, one_ne_zero, fun _ => 1, by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isChowFormCycle_zero F n k`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `ChowFormCycleAdd.proof ChowFormAssoc.proof F n k _ _ _ _ (hs a (Finset.mem_insert_self a s)) (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))`.
-/
theorem isChowFormCycle_sum {F : Type} [Field F] {n k : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (Z : ι → ProjCycle F n) (h : ι → MvPolynomial (Fin k × Fin n) F)
    (hs : ∀ i ∈ s, IsChowFormCycle (Z i) k (h i)) :
    IsChowFormCycle (∑ i ∈ s, Z i) k (∏ i ∈ s, h i) := by
  induction s using Finset.induction_on with
  | empty => simpa using isChowFormCycle_zero F n k
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact ChowFormCycleAdd.proof ChowFormAssoc.proof F n k _ _ _ _ (hs a (Finset.mem_insert_self a s))
      (ih fun i hi => hs i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Take `⟨d, hd, g, hg, rfl⟩` from `hZ`. Conclude with `⟨c * d, mul_ne_zero hc hd, g, hg, by rw [C_mul, mul_assoc]⟩`.
-/
theorem isChowFormCycle_C_mul {F : Type} [Field F] {n k : ℕ} {Z : ProjCycle F n}
    {h : MvPolynomial (Fin k × Fin n) F} {c : F} (hc : c ≠ 0) (hZ : IsChowFormCycle Z k h) :
    IsChowFormCycle Z k (C c * h) := by
  obtain ⟨d, hd, g, hg, rfl⟩ := hZ
  exact ⟨c * d, mul_ne_zero hc hd, g, hg, by rw [C_mul, mul_assoc]⟩

/- English proof (translation)
Take `⟨c1, hc1, g1, hg1, rfl⟩` from `ha`. Take `⟨c2, hc2, g2, hg2, rfl⟩` from `hb`. Establish `hex : ∀ W ∈ Z.support, ∃ d : F, d ≠ 0 ∧ g1 W = C d * g2 W` using `fun W hW => ChowFormAssoc.proof F n k W (g2 W) (g1 W) (hg2 W hW) (hg1 W hW)`. Set `d : Ideal (MvPolynomial (Fin n) F) → F` to `fun W => if h : W ∈ Z.support then (hex W h).choose else 1`. Establish `hd : ∀ W ∈ Z.support, d W ≠ 0 ∧ g1 W = C (d W) * g2 W` using `fun W hW => by`.

Simplify using `only [d, dif_pos hW]`. Conclude with `(hex W hW).choose_spec`. Establish `key : ∏ W ∈ Z.support, g1 W ^ Z W = C (∏ W ∈ Z.support, d W ^ Z W) * ∏ W ∈ Z.support, g2 W ^ Z W`. Rewrite using `[map_prod, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun W hW => ?_` and prove the remaining obligations.

Rewrite using `[map_pow, ← mul_pow, (hd W hW).2]`. Establish `hD : ∏ W ∈ Z.support, d W ^ Z W ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hd W hW).1`. Use `⟨c1 * (∏ W ∈ Z.support, d W ^ Z W) * c2⁻¹, mul_ne_zero (mul_ne_zero hc1 hD) (inv_ne_zero hc2), ?_⟩` and prove the remaining obligations. Rewrite using `[key, ← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul, mul_assoc (c1 * _), inv_mul_cancel₀ hc2, mul_one]`.
-/
theorem isChowFormCycle_unique {F : Type} [Field F] {n k : ℕ} {Z : ProjCycle F n}
    {a b : MvPolynomial (Fin k × Fin n) F} (ha : IsChowFormCycle Z k a) (hb : IsChowFormCycle Z k b) :
    ∃ c : F, c ≠ 0 ∧ a = C c * b := by
  classical
  obtain ⟨c1, hc1, g1, hg1, rfl⟩ := ha
  obtain ⟨c2, hc2, g2, hg2, rfl⟩ := hb
  have hex : ∀ W ∈ Z.support, ∃ d : F, d ≠ 0 ∧ g1 W = C d * g2 W := fun W hW =>
    ChowFormAssoc.proof F n k W (g2 W) (g1 W) (hg2 W hW) (hg1 W hW)
  let d : Ideal (MvPolynomial (Fin n) F) → F := fun W =>
    if h : W ∈ Z.support then (hex W h).choose else 1
  have hd : ∀ W ∈ Z.support, d W ≠ 0 ∧ g1 W = C (d W) * g2 W := fun W hW => by
    simp only [d, dif_pos hW]
    exact (hex W hW).choose_spec
  have key : ∏ W ∈ Z.support, g1 W ^ Z W =
      C (∏ W ∈ Z.support, d W ^ Z W) * ∏ W ∈ Z.support, g2 W ^ Z W := by
    rw [map_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun W hW => ?_
    rw [map_pow, ← mul_pow, (hd W hW).2]
  have hD : ∏ W ∈ Z.support, d W ^ Z W ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hd W hW).1
  refine ⟨c1 * (∏ W ∈ Z.support, d W ^ Z W) * c2⁻¹, mul_ne_zero (mul_ne_zero hc1 hD) (inv_ne_zero hc2), ?_⟩
  rw [key, ← mul_assoc, ← C_mul, ← mul_assoc, ← C_mul, mul_assoc (c1 * _), inv_mul_cancel₀ hc2, mul_one]

/- English proof (translation)
Take `⟨m, hm⟩` from `ne_zero_iff.mp hb`. Establish `hcoef` using `congrArg (coeff m) h`. Rewrite `hcoef` using `[coeff_map, coeff_C_mul, coeff_map]`. Establish `hσm : σ (coeff m b) ≠ 0` using `(map_ne_zero σ).mpr hm`. Establish `hcc : σ (coeff m a / coeff m b) = c`.

Rewrite using `[map_div₀, hcoef, mul_div_cancel_right₀ _ hσm]`. Use `⟨coeff m a / coeff m b, fun h0 => hc (by rw [← hcc, h0, map_zero]), ?_⟩` and prove the remaining obligations. Apply `map_injective σ σ.injective` to reduce the goal to its premises. Rewrite using `[h, map_mul, map_C, hcc]`.
-/
theorem eq_C_mul_of_map_eq {F K : Type*} [Field F] [Field K] (σ : F →+* K) {ι : Type*}
    {a b : MvPolynomial ι F} (hb : b ≠ 0) {c : K} (hc : c ≠ 0) (h : map σ a = C c * map σ b) :
    ∃ c₀ : F, c₀ ≠ 0 ∧ a = C c₀ * b := by
  obtain ⟨m, hm⟩ := ne_zero_iff.mp hb
  have hcoef := congrArg (coeff m) h
  rw [coeff_map, coeff_C_mul, coeff_map] at hcoef
  have hσm : σ (coeff m b) ≠ 0 := (map_ne_zero σ).mpr hm
  have hcc : σ (coeff m a / coeff m b) = c := by
    rw [map_div₀, hcoef, mul_div_cancel_right₀ _ hσm]
  refine ⟨coeff m a / coeff m b, fun h0 => hc (by rw [← hcc, h0, map_zero]), ?_⟩
  apply map_injective σ σ.injective
  rw [h, map_mul, map_C, hcc]

/- English proof (translation)
Unfold `specFirst`. Rewrite using `[map_bind₁]`. Establish `hvar : (fun ij => map σ (specFirstVar u ij)) = (specFirstVar (fun j => σ (u j)) : Fin (k + 1) × Fin n → MvPolynomial (Fin k × Fin n) S)`. Use function extensionality and compare the values at `ij`. Take `⟨i, j⟩` from `ij`.

Apply the tactic sequence `cases i using Fin.cases <;> simp [specFirstVar]`. Rewrite using `[hvar]`.
-/
theorem map_specFirst {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S) {k n : ℕ}
    (f : MvPolynomial (Fin (k + 1) × Fin n) R) (u : Fin n → R) :
    map σ (specFirst f u) = specFirst (map σ f) (fun j => σ (u j)) := by
  unfold specFirst
  rw [map_bind₁]
  have hvar : (fun ij => map σ (specFirstVar u ij)) =
      (specFirstVar (fun j => σ (u j)) : Fin (k + 1) × Fin n → MvPolynomial (Fin k × Fin n) S) := by
    funext ij
    obtain ⟨i, j⟩ := ij
    cases i using Fin.cases <;> simp [specFirstVar]
  rw [hvar]

/- English proof (translation)
Simplify using `[linForm]`.
-/
theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] (σ : R →+* S) {n : ℕ} (u : Fin n → R) :
    map σ (linForm u) = linForm (fun j => σ (u j)) := by
  simp [linForm]

/- English proof (translation)
Simplify using `[specFirst, map_mul, map_prod, map_pow]`.
-/
theorem specFirst_C_mul_prod {R : Type*} [CommRing R] {k n : ℕ} {ι : Type*} (s : Finset ι) (c : R)
    (g : ι → MvPolynomial (Fin (k + 1) × Fin n) R) (m : ι → ℕ) (u : Fin n → R) :
    specFirst (C c * ∏ i ∈ s, g i ^ m i) u = C c * ∏ i ∈ s, specFirst (g i) u ^ m i := by
  simp [specFirst, map_mul, map_prod, map_pow]

/- English proof (translation)
Rewrite `hW` using `[Finsupp.mem_support_iff]`. Assume the negation of the conclusion as `h`. Conclude with `hW (by simp [fundCycle, Finsupp.onFinset_apply, h])`.
-/
theorem mem_relComps_of_mem_support {R : Type*} [CommRing R] [IsNoetherianRing R] {n : ℕ}
    {J W : Ideal (MvPolynomial (Fin n) R)} (hW : W ∈ (fundCycle J).support) : W ∈ relComps J := by
  classical
  rw [Finsupp.mem_support_iff] at hW
  by_contra h
  exact hW (by simp [fundCycle, Finsupp.onFinset_apply, h])

end SectionPerfect

open SectionPerfect in

/- English proof (translation)
Introduce `F _ _ n e I f u hI hf hu`. Establish `hdimI` using `coneDimOfChowForm_full F n (e + 1) I f hI hf`. Establish `hWc : ∀ W ∈ (divCycle I u).support, IsProjPrime W ∧ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞)` using `fun W hW => ConeDimComponent.proof_closed F n e I W u hI hdimI hu (mem_relComps_of_mem_support hW)`. Set `g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin e × Fin n) F` to `fun W => if h : ∃ g, IsChowForm W e g then h.choose else 1`. Establish `hg : ∀ W ∈ (divCycle I u).support, IsChowForm W e (g W)` using `fun W hW => by`.

Establish `hex` using `chowFormExists_full F n e W (hWc W hW).1 (hWc W hW).2`. Simplify using `only [g, dif_pos hex]`. Conclude with `hex.choose_spec`. Set `K` to `AlgebraicClosure F`. Set `σ : F →+* K` to `algebraMap F K`.

Set `φ : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) K` to `MvPolynomial.map σ`. Set `uK : Fin n → K` to `fun j => σ (u j)`. Set `IK` to `I.map φ`. Establish `hIKh : IsHomogIdeal IK` using `isHomogIdeal_map σ hI.isHomog`. Establish `hIKr : IK.IsRadical` using `RadicalBaseChange.proof F K σ (Fin n) I hI.isPrime.isRadical`.

Establish `hfK : IsChowForm IK (e + 1) (map σ f)` using `chowFormExtend_full F K σ n (e + 1) I f hf`. Take `⟨c, hc, gP, hgP, hfKeq⟩` from `chowFormReduced_full K n (e + 1) IK (map σ f) hIKh hIKr hfK`. Establish `hcomap : ∀ P ∈ IK.minimalPrimes, P.comap φ = I` using `fun P hP => hM F K σ (Fin n) I hI.isPrime P hP`. Establish `hPu : ∀ P ∈ IK.minimalPrimes, linForm uK ∉ P`. Introduce `P hP hmem`.

Apply `hu` to reduce the goal to its premises. Rewrite using `[← hcomap P hP, Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `map σ (linForm u) ∈ P`. Rewrite using `[map_linForm]`. Conclude with `hmem`.

Establish `hPsupp : ∀ P ∈ IK.minimalPrimes, P ∈ (fundCycle IK).support`. Introduce `P hP`. Rewrite using `[mem_support_fundCycle_iff hIKr]`. Use `⟨hP, ?_⟩` and prove the remaining obligations. Take `⟨j, hj⟩` from `hI.isRelevant`.

Use `⟨j, fun hjP => hj ?_⟩` and prove the remaining obligations. Rewrite using `[← hcomap P hP, Ideal.mem_comap]`. Express the relevant statement in the definitionally equal form `map σ (X j) ∈ P`. Rewrite using `[map_X]`. Conclude with `hjP`.

Establish `hPdim : ∀ P ∈ IK.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞)` using `fun P hP => coneDimOfChowForm_full K n (e + 1) P (gP P) (isProjPrime_of_mem_support_fundCycle hIKh (hPsupp P hP)) (hgP P (hPsupp P hP))`. Establish `hL : IsChowFormCycle (∑ P ∈ (fundCycle IK).support, divCycle P uK) e (specFirst (map σ f) uK)`. Establish `h1 : IsChowFormCycle (∑ P ∈ (fundCycle IK).support, divCycle P uK) e (∏ P ∈ (fundCycle IK).support, specFirst (gP P) uK ^ fundCycle IK P)`. Use `isChowFormCycle_sum _ _ _ fun P hP => ?_` and prove the remaining obligations. Rewrite using `[fundCycle_apply_of_isRadical hIKr hP, pow_one]`.

Establish `hPmin` using `(mem_relComps_of_mem_support hP).1`. Conclude with `hA K n e P (gP P) uK (isProjPrime_of_mem_support_fundCycle hIKh hP) (hgP P hP) (hPu P hPmin)`. Rewrite using `[hfKeq, specFirst_C_mul_prod]`. Conclude with `isChowFormCycle_C_mul hc h1`. Establish `hsec : fundCycle (IK ⊔ Ideal.span {linForm uK}) = ∑ P ∈ (fundCycle IK).support, divCycle P uK` using `hS K n IK uK hIKr (fun P hP Q hQ => by rw [hPdim P hP, hPdim Q hQ]) hPu`.

Establish `hmapJ : (I ⊔ Ideal.span {linForm u}).map φ = IK ⊔ Ideal.span {linForm uK}`. Rewrite using `[Ideal.map_sup, Ideal.map_span, Set.image_singleton]`. Express the relevant statement in the definitionally equal form `IK ⊔ Ideal.span {map σ (linForm u)} = _`. Rewrite using `[map_linForm]`. Establish `hbase` using `hB F K σ n (I ⊔ Ideal.span {linForm u})`.

Establish `hR : IsChowFormCycle (∑ W ∈ (divCycle I u).support, divCycle I u W • fundCycle (W.map φ)) e (∏ W ∈ (divCycle I u).support, map σ (g W) ^ divCycle I u W)`. Use `isChowFormCycle_sum _ _ _ fun W hW => ?_` and prove the remaining obligations. Use `ChowFormCycleSmul.proof K n e _ _ _ ?_` and prove the remaining obligations. Conclude with `chowFormReduced_full K n e (W.map φ) (map σ (g W)) (isHomogIdeal_map σ (hWc W hW).1.isHomog) (RadicalBaseChange.proof F K σ (Fin n) W (hWc W hW).1.isPrime.isRadical) (chowFormExtend_full F K σ n e W (g W) (hg W hW))`. Establish `hcyc : ∑ P ∈ (fundCycle IK).support, divCycle P uK = ∑ W ∈ (divCycle I u).support, divCycle I u W • fundCycle (W.map φ)`.

Rewrite using `[← hsec, ← hmapJ]`. Conclude with `hbase`. Rewrite `hL` using `[hcyc]`. Take `⟨c', hc', hc'eq⟩` from `isChowFormCycle_unique hL hR`. Establish `hprod0 : ∏ W ∈ (divCycle I u).support, g W ^ divCycle I u W ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1`.

Establish `hmapeq : map σ (specFirst f u) = C c' * map σ (∏ W ∈ (divCycle I u).support, g W ^ divCycle I u W)`. Rewrite using `[map_specFirst, hc'eq, map_prod]`. Simplify using `only [map_pow]`. Take `⟨c₀, hc₀, heq⟩` from `eq_C_mul_of_map_eq σ hprod0 hc' hmapeq`. Conclude with `⟨c₀, hc₀, g, hg, heq⟩`.
-/
theorem chowFormSectionPerfect_of (hA : ChowFormSectionAlgClosed.Statement)
    (hS : SectionCycleReduced.Statement) (hM : MinimalPrimeComap.Statement)
    (hB : FundCycleBaseChange.Statement) : ChowFormSectionPerfect.Statement := by
  classical
  intro F _ _ n e I f u hI hf hu

  have hdimI := coneDimOfChowForm_full F n (e + 1) I f hI hf
  have hWc : ∀ W ∈ (divCycle I u).support, IsProjPrime W ∧
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := fun W hW =>
    ConeDimComponent.proof_closed F n e I W u hI hdimI hu (mem_relComps_of_mem_support hW)
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin e × Fin n) F :=
    fun W => if h : ∃ g, IsChowForm W e g then h.choose else 1
  have hg : ∀ W ∈ (divCycle I u).support, IsChowForm W e (g W) := fun W hW => by
    have hex := chowFormExists_full F n e W (hWc W hW).1 (hWc W hW).2
    simp only [g, dif_pos hex]
    exact hex.choose_spec

  let K := AlgebraicClosure F
  let σ : F →+* K := algebraMap F K
  let φ : MvPolynomial (Fin n) F →+* MvPolynomial (Fin n) K := MvPolynomial.map σ
  let uK : Fin n → K := fun j => σ (u j)
  let IK := I.map φ
  have hIKh : IsHomogIdeal IK := isHomogIdeal_map σ hI.isHomog
  have hIKr : IK.IsRadical := RadicalBaseChange.proof F K σ (Fin n) I hI.isPrime.isRadical
  have hfK : IsChowForm IK (e + 1) (map σ f) := chowFormExtend_full F K σ n (e + 1) I f hf
  obtain ⟨c, hc, gP, hgP, hfKeq⟩ := chowFormReduced_full K n (e + 1) IK (map σ f) hIKh hIKr hfK

  have hcomap : ∀ P ∈ IK.minimalPrimes, P.comap φ = I := fun P hP =>
    hM F K σ (Fin n) I hI.isPrime P hP
  have hPu : ∀ P ∈ IK.minimalPrimes, linForm uK ∉ P := by
    intro P hP hmem
    apply hu
    rw [← hcomap P hP, Ideal.mem_comap]
    change map σ (linForm u) ∈ P
    rw [map_linForm]
    exact hmem
  have hPsupp : ∀ P ∈ IK.minimalPrimes, P ∈ (fundCycle IK).support := by
    intro P hP
    rw [mem_support_fundCycle_iff hIKr]
    refine ⟨hP, ?_⟩
    obtain ⟨j, hj⟩ := hI.isRelevant
    refine ⟨j, fun hjP => hj ?_⟩
    rw [← hcomap P hP, Ideal.mem_comap]
    change map σ (X j) ∈ P
    rw [map_X]
    exact hjP
  have hPdim : ∀ P ∈ IK.minimalPrimes,
      ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ((e + 1 : ℕ) : WithBot ℕ∞) := fun P hP =>
    coneDimOfChowForm_full K n (e + 1) P (gP P)
      (isProjPrime_of_mem_support_fundCycle hIKh (hPsupp P hP)) (hgP P (hPsupp P hP))

  have hL : IsChowFormCycle (∑ P ∈ (fundCycle IK).support, divCycle P uK) e
      (specFirst (map σ f) uK) := by
    have h1 : IsChowFormCycle (∑ P ∈ (fundCycle IK).support, divCycle P uK) e
        (∏ P ∈ (fundCycle IK).support, specFirst (gP P) uK ^ fundCycle IK P) := by
      refine isChowFormCycle_sum _ _ _ fun P hP => ?_
      rw [fundCycle_apply_of_isRadical hIKr hP, pow_one]
      have hPmin := (mem_relComps_of_mem_support hP).1
      exact hA K n e P (gP P) uK (isProjPrime_of_mem_support_fundCycle hIKh hP) (hgP P hP)
        (hPu P hPmin)
    rw [hfKeq, specFirst_C_mul_prod]
    exact isChowFormCycle_C_mul hc h1
  have hsec : fundCycle (IK ⊔ Ideal.span {linForm uK}) =
      ∑ P ∈ (fundCycle IK).support, divCycle P uK :=
    hS K n IK uK hIKr (fun P hP Q hQ => by rw [hPdim P hP, hPdim Q hQ]) hPu
  have hmapJ : (I ⊔ Ideal.span {linForm u}).map φ = IK ⊔ Ideal.span {linForm uK} := by
    rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    change IK ⊔ Ideal.span {map σ (linForm u)} = _
    rw [map_linForm]

  have hbase := hB F K σ n (I ⊔ Ideal.span {linForm u})
  have hR : IsChowFormCycle
      (∑ W ∈ (divCycle I u).support, divCycle I u W • fundCycle (W.map φ)) e
      (∏ W ∈ (divCycle I u).support, map σ (g W) ^ divCycle I u W) := by
    refine isChowFormCycle_sum _ _ _ fun W hW => ?_
    refine ChowFormCycleSmul.proof K n e _ _ _ ?_
    exact chowFormReduced_full K n e (W.map φ) (map σ (g W)) (isHomogIdeal_map σ (hWc W hW).1.isHomog)
      (RadicalBaseChange.proof F K σ (Fin n) W (hWc W hW).1.isPrime.isRadical)
      (chowFormExtend_full F K σ n e W (g W) (hg W hW))
  have hcyc : ∑ P ∈ (fundCycle IK).support, divCycle P uK =
      ∑ W ∈ (divCycle I u).support, divCycle I u W • fundCycle (W.map φ) := by
    rw [← hsec, ← hmapJ]
    exact hbase
  rw [hcyc] at hL
  obtain ⟨c', hc', hc'eq⟩ := isChowFormCycle_unique hL hR

  have hprod0 : ∏ W ∈ (divCycle I u).support, g W ^ divCycle I u W ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hg W hW).1
  have hmapeq : map σ (specFirst f u) =
      C c' * map σ (∏ W ∈ (divCycle I u).support, g W ^ divCycle I u W) := by
    rw [map_specFirst, hc'eq, map_prod]
    simp only [map_pow]
  obtain ⟨c₀, hc₀, heq⟩ := eq_C_mul_of_map_eq σ hprod0 hc' hmapeq
  exact ⟨c₀, hc₀, g, hg, heq⟩

namespace SectionAlgClosed

variable {F : Type*} [Field F] {n : ℕ}

/- English proof (translation)
Establish `hmem : ∀ G : MvPolynomial (Fin k × Fin n) F, G ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v G = 0` using `fun G => by`. Simplify using `[incIdeal, Submodule.mem_iInf, RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, h⟩`. Use `⟨h0, ?_⟩` and prove the remaining obligations.

Use extensionality with `G`. Rewrite using `[hmem, Ideal.mem_span_singleton]`. Conclude with `h G`. Introduce and unpack `⟨h0, h⟩`. Use `⟨h0, fun G => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hmem, h, Ideal.mem_span_singleton]`.
-/
theorem isChowForm_iff_span {P : Ideal (MvPolynomial (Fin n) F)} {k : ℕ}
    {g : MvPolynomial (Fin k × Fin n) F} :
    IsChowForm P k g ↔ g ≠ 0 ∧ incIdeal P k = Ideal.span {g} := by
  have hmem : ∀ G : MvPolynomial (Fin k × Fin n) F,
      G ∈ incIdeal P k ↔ ∀ v ∈ incidence P k, aeval v G = 0 := fun G => by
    simp [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]
  constructor
  · rintro ⟨h0, h⟩
    refine ⟨h0, ?_⟩
    ext G
    rw [hmem, Ideal.mem_span_singleton]
    exact h G
  · rintro ⟨h0, h⟩
    refine ⟨h0, fun G => ?_⟩
    rw [← hmem, h, Ideal.mem_span_singleton]

/- English proof (translation)
Proceed by induction on `a using UniqueFactorizationMonoid.induction_on_prime generalizing b with`. Consider the case `h₁ => exact absurd rfl ha`. Consider the case `h₂ x hx => exact hx.dvd`. Consider the case `h₃ a p ha' hp ih`. Establish `hpp : emultiplicity p p = 1` using `(FiniteMultiplicity.of_not_isUnit hp.not_isUnit hp.ne_zero).emultiplicity_self`.

Establish `hpb : p ∣ b`. Apply `dvd_of_emultiplicity_pos` to reduce the goal to its premises. Use `h p hp.irreducible` as an intermediate fact. Rewrite `this` using `[emultiplicity_mul hp, hpp]`. Conclude with `lt_of_lt_of_le (by simp) this`.

Take `⟨b', rfl⟩` from `hpb`. Establish `hb' : b' ≠ 0` using `right_ne_zero_of_mul hb`. Use `mul_dvd_mul_left p (ih ha' hb' fun q hq => ?_)` and prove the remaining obligations. Establish `hqp : Prime q` using `hq.prime`. Establish `hfin : emultiplicity q p ≠ ⊤`.

Rewrite using `[Ne, emultiplicity_eq_top, not_not]`. Conclude with `FiniteMultiplicity.of_not_isUnit hqp.not_isUnit hp.ne_zero`. Use `h q hq` as an intermediate fact. Rewrite `this` using `[emultiplicity_mul hqp, emultiplicity_mul hqp]`. Conclude with `(WithTop.add_le_add_iff_left hfin).mp this`.
-/
theorem dvd_of_forall_emultiplicity_le' {R : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] {a b : R} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ p, Irreducible p → emultiplicity p a ≤ emultiplicity p b) : a ∣ b := by
  induction a using UniqueFactorizationMonoid.induction_on_prime generalizing b with
  | h₁ => exact absurd rfl ha
  | h₂ x hx => exact hx.dvd
  | h₃ a p ha' hp ih =>
    have hpp : emultiplicity p p = 1 :=
      (FiniteMultiplicity.of_not_isUnit hp.not_isUnit hp.ne_zero).emultiplicity_self
    have hpb : p ∣ b := by
      apply dvd_of_emultiplicity_pos
      have := h p hp.irreducible
      rw [emultiplicity_mul hp, hpp] at this
      exact lt_of_lt_of_le (by simp) this
    obtain ⟨b', rfl⟩ := hpb
    have hb' : b' ≠ 0 := right_ne_zero_of_mul hb
    refine mul_dvd_mul_left p (ih ha' hb' fun q hq => ?_)
    have hqp : Prime q := hq.prime
    have hfin : emultiplicity q p ≠ ⊤ := by
      rw [Ne, emultiplicity_eq_top, not_not]
      exact FiniteMultiplicity.of_not_isUnit hqp.not_isUnit hp.ne_zero
    have := h q hq
    rw [emultiplicity_mul hqp, emultiplicity_mul hqp] at this
    exact (WithTop.add_le_add_iff_left hfin).mp this

end SectionAlgClosed

open SectionAlgClosed in

/- English proof (translation)
Establish `h₁ : ConeDimOfChowForm.Statement` using `SectionPerfect.coneDimOfChowForm_full`. Establish `h₂ : ConeDimComponent.Statement` using `ConeDimComponent.proof_closed`. Establish `h₃ : ChowFormExists.Statement` using `SectionPerfect.chowFormExists_full`. Establish `h₄ : IncIdealPrime.Statement` using `SectionPerfect.incIdealPrime_full`. Introduce `F _ _ n e I f u hI hf hu`.

Take `⟨hh0, hord⟩` from `h₅ F n e I f u hI hf hu`. Establish `hdim` using `h₁ F n (e + 1) I f hI hf`. Establish `hcomp : ∀ W ∈ (divCycle I u).support, W ∈ relComps (I ⊔ Ideal.span {linForm u})`. Introduce `W hW`. Rewrite `hW` using `[Finsupp.mem_support_iff]`.

Assume the negation of the conclusion as `h`. Conclude with `hW (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])`. Establish `hW1 : ∀ W ∈ (divCycle I u).support, IsProjPrime W ∧ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞)` using `fun W hW => h₂ F n e I W u hI hdim hu (hcomp W hW)`. Establish `hex : ∀ W ∈ (divCycle I u).support, ∃ g, IsChowForm W e g` using `fun W hW => h₃ F n e W (hW1 W hW).1 (hW1 W hW).2`. Set `g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin e × Fin n) F` to `fun W => if h : ∃ g, IsChowForm W e g then h.choose else 1`.

Establish `hg : ∀ W ∈ (divCycle I u).support, IsChowForm W e (g W)` using `fun W hW => by`. Simplify using `only [g, dif_pos (hex W hW)]`. Conclude with `(hex W hW).choose_spec`. Establish `hspan : ∀ W ∈ (divCycle I u).support, incIdeal W e = Ideal.span {g W}` using `fun W hW => (isChowForm_iff_span.mp (hg W hW)).2`. Establish `hgprime : ∀ W ∈ (divCycle I u).support, Prime (g W)`.

Introduce `W hW`. Establish `hp` using `h₄ F n e W (hW1 W hW).1.isPrime (hW1 W hW).1.isRelevant`. Rewrite `hp` using `[hspan W hW]`. Conclude with `(Ideal.span_singleton_prime (isChowForm_iff_span.mp (hg W hW)).1).mp hp`. Use `set Pr := ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W with hPr`.

Establish `hPr0 : Pr ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hgprime W hW).ne_zero`. Establish `hmult : ∀ q, Irreducible q → emultiplicity q Pr = emultiplicity q (specFirst f u)`. Introduce `q hq`. Establish `hqp : Prime q` using `hq.prime`. Rewrite using `[hord q hq, hPr, Finset.emultiplicity_prod hqp, Finset.sum_filter]`.

Use `Finset.sum_congr rfl fun W hW => ?_` and prove the remaining obligations. Rewrite using `[emultiplicity_pow hqp]`. Use `split_ifs with hs`. Establish `hass : Associated q (g W)`. Rewrite using `[← Ideal.span_singleton_eq_span_singleton, hs, hspan W hW]`.

Rewrite using `[← emultiplicity_eq_of_associated_left hass, (FiniteMultiplicity.of_not_isUnit (hgprime W hW).not_isUnit (hgprime W hW).ne_zero).emultiplicity_self, mul_one]`. Establish `: emultiplicity q (g W) = 0`. Rewrite using `[emultiplicity_eq_zero]`. Introduce `hdvd`. Apply `hs` to reduce the goal to its premises.

Rewrite using `[hspan W hW, Ideal.span_singleton_eq_span_singleton]`. Conclude with `hq.associated_of_dvd (hgprime W hW).irreducible hdvd`. Rewrite using `[this, mul_zero]`. Establish `hass : Associated Pr (specFirst f u)` using `associated_of_dvd_dvd (dvd_of_forall_emultiplicity_le' hPr0 hh0 fun q hq => (hmult q hq).le) (dvd_of_forall_emultiplicity_le' hh0 hPr0 fun q hq => (hmult q hq).ge)`. Take `⟨v, hv⟩` from `hass`.

Take `⟨c, hc, hvc⟩` from `(isUnit_iff_eq_C_of_isReduced (P := (v : MvPolynomial (Fin e × Fin n) F))).mp v.isUnit`. Use `⟨c, hc.ne_zero, g, hg, ?_⟩` and prove the remaining obligations. Rewrite using `[← hv, hvc, mul_comm]`.
-/
theorem chowFormSectionAlgClosed_of (h₅ : SectionOrderAlgClosed.Statement) :
    ChowFormSectionAlgClosed.Statement := by
  have h₁ : ConeDimOfChowForm.Statement := SectionPerfect.coneDimOfChowForm_full
  have h₂ : ConeDimComponent.Statement := ConeDimComponent.proof_closed
  have h₃ : ChowFormExists.Statement := SectionPerfect.chowFormExists_full
  have h₄ : IncIdealPrime.Statement := SectionPerfect.incIdealPrime_full
  intro F _ _ n e I f u hI hf hu
  classical
  obtain ⟨hh0, hord⟩ := h₅ F n e I f u hI hf hu
  have hdim := h₁ F n (e + 1) I f hI hf
  have hcomp : ∀ W ∈ (divCycle I u).support, W ∈ relComps (I ⊔ Ideal.span {linForm u}) := by
    intro W hW
    rw [Finsupp.mem_support_iff] at hW
    by_contra h
    exact hW (by simp [divCycle, fundCycle, Finsupp.onFinset_apply, h])
  have hW1 : ∀ W ∈ (divCycle I u).support, IsProjPrime W ∧
      ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := fun W hW =>
    h₂ F n e I W u hI hdim hu (hcomp W hW)
  have hex : ∀ W ∈ (divCycle I u).support, ∃ g, IsChowForm W e g := fun W hW =>
    h₃ F n e W (hW1 W hW).1 (hW1 W hW).2
  let g : Ideal (MvPolynomial (Fin n) F) → MvPolynomial (Fin e × Fin n) F :=
    fun W => if h : ∃ g, IsChowForm W e g then h.choose else 1
  have hg : ∀ W ∈ (divCycle I u).support, IsChowForm W e (g W) := fun W hW => by
    simp only [g, dif_pos (hex W hW)]
    exact (hex W hW).choose_spec
  have hspan : ∀ W ∈ (divCycle I u).support, incIdeal W e = Ideal.span {g W} := fun W hW =>
    (isChowForm_iff_span.mp (hg W hW)).2
  have hgprime : ∀ W ∈ (divCycle I u).support, Prime (g W) := by
    intro W hW
    have hp := h₄ F n e W (hW1 W hW).1.isPrime (hW1 W hW).1.isRelevant
    rw [hspan W hW] at hp
    exact (Ideal.span_singleton_prime (isChowForm_iff_span.mp (hg W hW)).1).mp hp
  set Pr := ∏ W ∈ (divCycle I u).support, g W ^ (divCycle I u) W with hPr
  have hPr0 : Pr ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun W hW => pow_ne_zero _ (hgprime W hW).ne_zero
  have hmult : ∀ q, Irreducible q → emultiplicity q Pr = emultiplicity q (specFirst f u) := by
    intro q hq
    have hqp : Prime q := hq.prime
    rw [hord q hq, hPr, Finset.emultiplicity_prod hqp, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [emultiplicity_pow hqp]
    split_ifs with hs
    · have hass : Associated q (g W) := by
        rw [← Ideal.span_singleton_eq_span_singleton, hs, hspan W hW]
      rw [← emultiplicity_eq_of_associated_left hass,
        (FiniteMultiplicity.of_not_isUnit (hgprime W hW).not_isUnit (hgprime W hW).ne_zero).emultiplicity_self,
        mul_one]
    · have : emultiplicity q (g W) = 0 := by
        rw [emultiplicity_eq_zero]
        intro hdvd
        apply hs
        rw [hspan W hW, Ideal.span_singleton_eq_span_singleton]
        exact hq.associated_of_dvd (hgprime W hW).irreducible hdvd
      rw [this, mul_zero]
  have hass : Associated Pr (specFirst f u) :=
    associated_of_dvd_dvd
      (dvd_of_forall_emultiplicity_le' hPr0 hh0 fun q hq => (hmult q hq).le)
      (dvd_of_forall_emultiplicity_le' hh0 hPr0 fun q hq => (hmult q hq).ge)
  obtain ⟨v, hv⟩ := hass
  obtain ⟨c, hc, hvc⟩ := (isUnit_iff_eq_C_of_isReduced (P := (v : MvPolynomial (Fin e × Fin n) F))).mp
    v.isUnit
  refine ⟨c, hc.ne_zero, g, hg, ?_⟩
  rw [← hv, hvc, mul_comm]

/- English proof (translation)
Introduce `F _ n J u hJ hdim hu`. Establish `hrelJ : ∀ P ∈ J.minimalPrimes, IsRelevant P`. Introduce `P hP`. Assume the negation of the conclusion as `h`. Apply `hu P hP` to reduce the goal to its premises.

Establish `hX : ∀ j, X j ∈ P` using `fun j => by`. Assume the negation of the conclusion as `hj`. Conclude with `h ⟨j, hj⟩`. Conclude with `Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hX j)`. Establish `hsupp : (fundCycle J).support = (J.finite_minimalPrimes_of_isNoetherianRing _).toFinset`.

Use extensionality with `P`. Rewrite using `[mem_support_fundCycle_iff hJ, Set.Finite.mem_toFinset]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, hrelJ P h⟩⟩`. Establish `happ : ∀ I W : Ideal (MvPolynomial (Fin n) F), fundCycle I W = if W ∈ relComps I then localMult I W else 0`. Introduce `I W`.

Unfold `fundCycle`. Rewrite using `[Finsupp.onFinset_apply]`. Establish `hcomp` using `hC F n J (linForm u) hdim hu`. Rewrite using `[hsupp]`. Use extensionality with `W`.

Rewrite using `[Finsupp.finsetSum_apply]`. Simplify using `only [divCycle, happ]`. Distinguish the cases in `hW : W ∈ relComps (J ⊔ Ideal.span {linForm u})`. Rewrite using `[if_pos hW, hL _ J W (linForm u) hJ hu hW.1 (fun P hP hPW => (hcomp P hP W).2 ⟨hW.1, hPW⟩), Finset.sum_filter]`. Use `Finset.sum_congr rfl fun P hP => ?_` and prove the remaining obligations.

Rewrite `hP` using `[Set.Finite.mem_toFinset]`. Distinguish the cases in `hPW : P ≤ W`. Rewrite using `[if_pos hPW, if_pos ⟨(hcomp P hP W).2 ⟨hW.1, hPW⟩, hW.2⟩]`. Rewrite using `[if_neg hPW, if_neg fun h => hPW ((hcomp P hP W).1 h.1).2]`. Rewrite using `[if_neg hW]`.

Use `symm`. Use `Finset.sum_eq_zero fun P hP => ?_` and prove the remaining obligations. Rewrite `hP` using `[Set.Finite.mem_toFinset]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨h1, h2⟩`.

Conclude with `hW ⟨((hcomp P hP W).1 h1).1, h2⟩`.
-/
theorem sectionCycleReduced_of (hC : SectionComponents.Statement)
    (hL : SectionLengthSum.Statement) : SectionCycleReduced.Statement := by
  classical
  intro F _ n J u hJ hdim hu

  have hrelJ : ∀ P ∈ J.minimalPrimes, IsRelevant P := by
    intro P hP
    by_contra h
    apply hu P hP
    have hX : ∀ j, X j ∈ P := fun j => by
      by_contra hj
      exact h ⟨j, hj⟩
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hX j)
  have hsupp : (fundCycle J).support = (J.finite_minimalPrimes_of_isNoetherianRing _).toFinset := by
    ext P
    rw [mem_support_fundCycle_iff hJ, Set.Finite.mem_toFinset]
    exact ⟨fun h => h.1, fun h => ⟨h, hrelJ P h⟩⟩
  have happ : ∀ I W : Ideal (MvPolynomial (Fin n) F),
      fundCycle I W = if W ∈ relComps I then localMult I W else 0 := by
    intro I W
    unfold fundCycle
    rw [Finsupp.onFinset_apply]
  have hcomp := hC F n J (linForm u) hdim hu
  rw [hsupp]
  ext W
  rw [Finsupp.finsetSum_apply]
  simp only [divCycle, happ]
  by_cases hW : W ∈ relComps (J ⊔ Ideal.span {linForm u})
  · rw [if_pos hW, hL _ J W (linForm u) hJ hu hW.1
      (fun P hP hPW => (hcomp P hP W).2 ⟨hW.1, hPW⟩), Finset.sum_filter]
    refine Finset.sum_congr rfl fun P hP => ?_
    rw [Set.Finite.mem_toFinset] at hP
    by_cases hPW : P ≤ W
    · rw [if_pos hPW, if_pos ⟨(hcomp P hP W).2 ⟨hW.1, hPW⟩, hW.2⟩]
    · rw [if_neg hPW, if_neg fun h => hPW ((hcomp P hP W).1 h.1).2]
  · rw [if_neg hW]
    symm
    refine Finset.sum_eq_zero fun P hP => ?_
    rw [Set.Finite.mem_toFinset] at hP
    rw [if_neg]
    rintro ⟨h1, h2⟩
    exact hW ⟨((hcomp P hP W).1 h1).1, h2⟩

end GlobalTheory.CompanionTheory.Ar.Short.ChowClosing
