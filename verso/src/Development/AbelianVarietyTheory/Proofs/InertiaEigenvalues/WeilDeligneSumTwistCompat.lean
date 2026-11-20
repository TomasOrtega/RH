import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsExhaustionGL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsMultisegments
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WDListLaws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

/- English proof (translation)
Rewrite using `[WD.lpZero, WD.lpTwist_mk]`. Conclude with `WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩`.
-/
theorem lpTwist_lpZero (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (WD.lpZero h).lpTwist ξ hξ = WD.lpZero h := by
  rw [WD.lpZero, WD.lpTwist_mk]
  exact WD.sound ⟨.refl _ _, fun σ v => Subsingleton.elim _ _, fun v => Subsingleton.elim _ _⟩

/- English proof (translation)
Proceed by induction on `x using WD.ind with`. Consider the case `hP n a`. Proceed by induction on `y using WD.ind with`. Consider the case `hP m b`. Rewrite using `[WD.lpSum_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpSum_mk]`.

Use `WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem lpTwist_lpSum (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpSum_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpSum_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  rfl

/- English proof (translation)
Proceed by induction on `x using WD.ind with`. Consider the case `hP n a`. Proceed by induction on `y using WD.ind with`. Consider the case `hP m b`. Rewrite using `[WD.lpChar_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpChar_mk]`.

Use `WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩` and prove the remaining obligations. Simplify using `only [WDRep.tensor_ρ, WDRep.twist_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left, LinearMap.smul_apply]`.
-/
theorem lpTwist_lpChar (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ) :
    (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y := by
  induction x using WD.ind with
  | hP n a =>
  induction y using WD.ind with
  | hP m b =>
  rw [WD.lpChar_mk, WD.lpTwist_mk, WD.lpTwist_mk, WD.lpChar_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  simp only [WDRep.tensor_ρ, WDRep.twist_ρ, LinearEquiv.refl_apply, TensorProduct.map_smul_left,
    LinearMap.smul_apply]

/- English proof (translation)
Proceed by induction on `x using WD.ind with`. Consider the case `hP n a`. Rewrite using `[WD.lpZero, WD.lpChar_mk]`. Use `haveI : Subsingleton (TensorProduct ℂ (Fin n → ℂ) (Fin 0 → ℂ)) := by`. Use `⟨fun u v => ?_⟩` and prove the remaining obligations.

Establish `key : ∀ z : TensorProduct ℂ (Fin n → ℂ) (Fin 0 → ℂ), z = 0` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rfl`. Consider the case `tmul p q => rw [Subsingleton.elim q 0, TensorProduct.tmul_zero]`. Consider the case `add p q hp hq => rw [hp, hq, add_zero]`.

Rewrite using `[key u, key v]`. Conclude with `WD.sound ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩`.
-/
theorem lpChar_lpZero (x : WD h) : x.lpChar (WD.lpZero h) = WD.lpZero h := by
  induction x using WD.ind with
  | hP n a =>
  rw [WD.lpZero, WD.lpChar_mk]
  haveI : Subsingleton (TensorProduct ℂ (Fin n → ℂ) (Fin 0 → ℂ)) := by
    refine ⟨fun u v => ?_⟩
    have key : ∀ z : TensorProduct ℂ (Fin n → ℂ) (Fin 0 → ℂ), z = 0 := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => rfl
      | tmul p q => rw [Subsingleton.elim q 0, TensorProduct.tmul_zero]
      | add p q hp hq => rw [hp, hq, add_zero]
    rw [key u, key v]
  exact WD.sound ⟨0, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

/- English proof (translation)
Proceed by induction on `x using WD.ind with`. Consider the case `hP n c`. Proceed by induction on `a using WD.ind with`. Consider the case `hP m a`. Proceed by induction on `b using WD.ind with`.

Consider the case `hP k b`. Rewrite using `[WD.lpSum_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpSum_mk]`. Use `WD.sound ⟨TensorProduct.prodRight ℂ ℂ _ _ _, fun σ v => ?_, fun v => ?_⟩` and prove the remaining obligations. Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`.

Consider the case `tmul p q`. Take `⟨q₁, q₂⟩` from `q`. Simplify using the standard rewrite rules. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Proceed by induction on `v using TensorProduct.induction_on with`.

Consider the case `zero => simp only [map_zero]`. Consider the case `tmul p q`. Take `⟨q₁, q₂⟩` from `q`. Simplify using `[TensorProduct.tmul_add]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`.
-/
theorem lpChar_lpSum (x a b : WD h) : x.lpChar (a.lpSum b) = (x.lpChar a).lpSum (x.lpChar b) := by
  induction x using WD.ind with
  | hP n c =>
  induction a using WD.ind with
  | hP m a =>
  induction b using WD.ind with
  | hP k b =>
  rw [WD.lpSum_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpChar_mk, WD.lpSum_mk]
  refine WD.sound ⟨TensorProduct.prodRight ℂ ℂ _ _ _, fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp
    | add p q hp hq => simp only [map_add, hp, hq]
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul p q =>
      obtain ⟨q₁, q₂⟩ := q
      simp [TensorProduct.tmul_add]
    | add p q hp hq => simp only [map_add, hp, hq]

/- English proof (translation)
The claim follows from `Polynomial.eq_one_of_monic_natDegree_zero (WD.charPol_monic _ σ) ((WD.charPol_natDegree _ σ).trans (WD.lpDim_zero h))`.
-/
theorem charPol_lpZero (σ : Weil h) : (WD.lpZero h).charPol σ = 1 :=
  Polynomial.eq_one_of_monic_natDegree_zero (WD.charPol_monic _ σ)
    ((WD.charPol_natDegree _ σ).trans (WD.lpDim_zero h))

end GlobalTheory.WDListLaws

open GlobalTheory.WDListLaws in

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ A w h`. Use `⟨fun l l' hp => ?_, fun l ξ hξ => ?_, fun x y ξ hξ => ⟨lpTwist_lpSum x y ξ hξ, lpTwist_lpChar x y ξ hξ⟩, fun x l => ?_, fun l => ⟨?_, fun σ => ?_⟩⟩` and prove the remaining obligations. Proceed by induction on `hp with`. Consider the case `nil => rfl`. Consider the case `cons x _ ih => show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)`.

Rewrite using `[ih]`. Consider the case `swap x y l => show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))`. Rewrite using `[← WD.lpSum_assoc, WD.lpSum_comm y x, WD.lpSum_assoc]`. Consider the case `trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂`. Proceed by induction on `l with`.

Consider the case `nil => exact lpTwist_lpZero ξ hξ`. Consider the case `cons x l ih => show (WD.lpSum x (sumList l)).lpTwist ξ hξ = WD.lpSum _ (sumList _)`. Rewrite using `[lpTwist_lpSum, ih]`. Proceed by induction on `l with`. Consider the case `nil => exact lpChar_lpZero x`.

Consider the case `cons y l ih => show x.lpChar (WD.lpSum y (sumList l)) = WD.lpSum _ (sumList _)`. Rewrite using `[lpChar_lpSum, ih]`. Proceed by induction on `l with`. Consider the case `nil => exact WD.lpDim_zero h`. Consider the case `cons y l ih => show (WD.lpSum y (sumList l)).lpDim = _`.

Rewrite using `[WD.lpDim_sum, ih, List.map_cons, List.sum_cons]`. Proceed by induction on `l with`. Consider the case `nil => exact charPol_lpZero σ`. Consider the case `cons y l ih => show (WD.lpSum y (sumList l)).charPol σ = _`. Rewrite using `[WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]`.
-/
theorem GlobalTheory.sumList_laws : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ l l' : List (WD h), l.Perm l' → sumList l = sumList l') ∧ (∀ (l : List (WD h)) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (sumList l).lpTwist ξ hξ = sumList (l.map fun y => y.lpTwist ξ hξ)) ∧ (∀ (x y : WD h) (ξ : Weil h →* ℂˣ) (hξ : GlobalTheory.WeilDeligne.IsSmooth ξ), (x.lpSum y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpSum (y.lpTwist ξ hξ) ∧ (x.lpChar y).lpTwist ξ hξ = (x.lpTwist ξ hξ).lpChar y) ∧ (∀ (x : WD h) (l : List (WD h)), x.lpChar (sumList l) = sumList (l.map x.lpChar)) ∧ (∀ l : List (WD h), (sumList l).lpDim = (l.map WD.lpDim).sum ∧ ∀ σ, (sumList l).charPol σ = (l.map fun y => y.charPol σ).prod) := by
  intro E Ω _ _ _ _ _ A w h
  refine ⟨fun l l' hp => ?_, fun l ξ hξ => ?_, fun x y ξ hξ => ⟨lpTwist_lpSum x y ξ hξ, lpTwist_lpChar x y ξ hξ⟩,
    fun x l => ?_, fun l => ⟨?_, fun σ => ?_⟩⟩
  · induction hp with
    | nil => rfl
    | cons x _ ih =>
      show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)
      rw [ih]
    | swap x y l =>
      show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))
      rw [← WD.lpSum_assoc, WD.lpSum_comm y x, WD.lpSum_assoc]
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  · induction l with
    | nil => exact lpTwist_lpZero ξ hξ
    | cons x l ih =>
      show (WD.lpSum x (sumList l)).lpTwist ξ hξ = WD.lpSum _ (sumList _)
      rw [lpTwist_lpSum, ih]
  · induction l with
    | nil => exact lpChar_lpZero x
    | cons y l ih =>
      show x.lpChar (WD.lpSum y (sumList l)) = WD.lpSum _ (sumList _)
      rw [lpChar_lpSum, ih]
  · induction l with
    | nil => exact WD.lpDim_zero h
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).lpDim = _
      rw [WD.lpDim_sum, ih, List.map_cons, List.sum_cons]
  · induction l with
    | nil => exact charPol_lpZero σ
    | cons y l ih =>
      show (WD.lpSum y (sumList l)).charPol σ = _
      rw [WD.charPol_lpSum, ih, List.map_cons, List.prod_cons]
