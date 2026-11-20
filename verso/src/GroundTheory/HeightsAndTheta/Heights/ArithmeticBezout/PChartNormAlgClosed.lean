import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartFirstGroupDvd
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormAlgClosed
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormSep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartNormAlgClosed

section Chart

variable {F : Type} [Field F] {n e : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F)
  (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime]

/- English proof (translation)
Rewrite using `[← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]`.
-/
theorem algebraMap_tower (x : MvPolynomial (Fin e × Fin n) F) :
    algebraMap (Localization.AtPrime p) (ChartLoc I t e p) (algebraMap _ _ x) =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) := by
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Use `show Ideal.Quotient.mk _ (rename Sum.inl (C c)) = Ideal.Quotient.mk _ (rename Sum.inr (C c))`. Simplify using `only [rename_C]`.
-/
theorem chartX_C (c : F) :
    chartX I t e (C c) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C c) := by
  show Ideal.Quotient.mk _ (rename Sum.inl (C c)) = Ideal.Quotient.mk _ (rename Sum.inr (C c))
  simp only [rename_C]

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply F (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p), MvPolynomial.algebraMap_eq]`.
-/
theorem algebraMap_localization_C (c : F) :
    algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p) (C c) =
      algebraMap F (Localization.AtPrime p) c := by
  rw [IsScalarTower.algebraMap_apply F (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p),
    MvPolynomial.algebraMap_eq]

/- English proof (translation)
Simplify using `only [chartLin, linForm, map_sum, map_mul, Algebra.smul_def]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[← algebraMap_localization_C p, algebraMap_tower, chartX_C]`.
-/
theorem chartLin_eq_sum (u : Fin n → F) :
    algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u) =
      ∑ m, algebraMap F (Localization.AtPrime p) (u m) •
        algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) := by
  simp only [chartLin, linForm, map_sum, map_mul, Algebra.smul_def]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← algebraMap_localization_C p, algebraMap_tower, chartX_C]

/- English proof (translation)
Establish `h : chartX I t e (linForm t - 1) = 0`. Conclude with `(Ideal.Quotient.eq_zero_iff_mem (I := chartIncIdeal I t e)).mpr (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))`. Rewrite `h` using `[map_sub, map_one, sub_eq_zero]`. Conclude with `h`.
-/
theorem chartLin_self : chartLin I t e t = 1 := by
  have h : chartX I t e (linForm t - 1) = 0 := by
    exact (Ideal.Quotient.eq_zero_iff_mem (I := chartIncIdeal I t e)).mpr
      (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))))
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h

/- English proof (translation)
Use `set A := Algebra.adjoin (Localization.AtPrime p) (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))`. Establish `hS : ∀ x : MvPolynomial (Fin e × Fin n) F, algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) ∈ A`. Introduce `x`. Rewrite using `[← algebraMap_tower]`. Conclude with `Subalgebra.algebraMap_mem A _`.

Set `π : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e` to `Ideal.Quotient.mk (chartIncIdeal I t e)`. Establish `hSig : ∀ y : MvPolynomial (Fin n ⊕ Fin e × Fin n) F, algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) ∈ A`. Introduce `y`. Proceed by induction on `y using MvPolynomial.induction_on with`. Consider the case `C a`.

Establish `h : π (C a) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a)` using `by show _ = Ideal.Quotient.mk _ (rename Sum.inr (C a))`. Rewrite using `[rename_C]`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `hS _`.

Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add]`. Conclude with `add_mem ha hb`. Consider the case `mul_X a v ha`. Rewrite using `[map_mul, map_mul]`.

Use `mul_mem ha ?_` and prove the remaining obligations. Break down `v with m | im` into its components or cases. Use `Algebra.subset_adjoin ⟨m, ?_⟩ show algebraMap (ChartInc I t e) (ChartLoc I t e p) ((Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X m)) : ChartInc I t e)) = _` and prove the remaining obligations. Rewrite using `[rename_X]`. Both sides reduce to the same expression.

Establish `h : π (X (Sum.inr im)) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im)` using `by show _ = Ideal.Quotient.mk _ (rename Sum.inr (X im))`. Rewrite using `[rename_X]`. Both sides reduce to the same expression. Rewrite using `[h]`. Conclude with `hS _`.

Rewrite using `[eq_top_iff]`. Introduce `z _`. Take `⟨⟨x, s⟩, rfl⟩` from `IsLocalization.mk'_surjective (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl) z`. Take `⟨s₀, hs₀, hs⟩` from `s.2`. Take `⟨y, rfl⟩ : ∃ y, π y = x` from `Ideal.Quotient.mk_surjective x`.

Use `set w := algebraMap (Localization.AtPrime p) (ChartLoc I t e p) (IsLocalization.mk' (Localization.AtPrime p) (1 : MvPolynomial (Fin e × Fin n) F) ⟨s₀, hs₀⟩)`. Establish `hw : algebraMap (ChartInc I t e) (ChartLoc I t e p) (s : ChartInc I t e) * w = 1`. Rewrite using `[← hs, ← algebraMap_tower, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one, IsLocalization.mk'_self, map_one]`. Establish `hz : IsLocalization.mk' (ChartLoc I t e p) (π y) s = algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) * w`. Rewrite using `[IsLocalization.mk'_eq_iff_eq_mul, mul_assoc, mul_comm w, hw, mul_one]`.

Use `show IsLocalization.mk' (ChartLoc I t e p) (π y) s ∈ A`. Rewrite using `[hz]`. Conclude with `mul_mem (hSig y) (Subalgebra.algebraMap_mem A _)`.
-/
theorem adjoin_eq_top :
    Algebra.adjoin (Localization.AtPrime p)
        (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m))) = ⊤ := by
  set A := Algebra.adjoin (Localization.AtPrime p)
    (Set.range fun m => algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)))
  have hS : ∀ x : MvPolynomial (Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (algebraMap _ (ChartInc I t e) x) ∈ A := by
    intro x
    rw [← algebraMap_tower]
    exact Subalgebra.algebraMap_mem A _
  let π : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk (chartIncIdeal I t e)
  have hSig : ∀ y : MvPolynomial (Fin n ⊕ Fin e × Fin n) F,
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) ∈ A := by
    intro y
    induction y using MvPolynomial.induction_on with
    | C a =>
      have h : π (C a) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (C a) := by
        show _ = Ideal.Quotient.mk _ (rename Sum.inr (C a))
        rw [rename_C]
        rfl
      rw [h]
      exact hS _
    | add a b ha hb =>
      rw [map_add, map_add]
      exact add_mem ha hb
    | mul_X a v ha =>
      rw [map_mul, map_mul]
      refine mul_mem ha ?_
      rcases v with m | im
      · refine Algebra.subset_adjoin ⟨m, ?_⟩
        show algebraMap (ChartInc I t e) (ChartLoc I t e p)
          ((Ideal.Quotient.mk (chartIncIdeal I t e) (rename Sum.inl (X m)) : ChartInc I t e)) = _
        rw [rename_X]
        rfl
      · have h : π (X (Sum.inr im)) = algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e) (X im) := by
          show _ = Ideal.Quotient.mk _ (rename Sum.inr (X im))
          rw [rename_X]
          rfl
        rw [h]
        exact hS _
  rw [eq_top_iff]
  intro z _
  obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (Algebra.algebraMapSubmonoid (ChartInc I t e) p.primeCompl) z
  obtain ⟨s₀, hs₀, hs⟩ := s.2
  obtain ⟨y, rfl⟩ : ∃ y, π y = x := Ideal.Quotient.mk_surjective x
  set w := algebraMap (Localization.AtPrime p) (ChartLoc I t e p)
    (IsLocalization.mk' (Localization.AtPrime p) (1 : MvPolynomial (Fin e × Fin n) F) ⟨s₀, hs₀⟩)
  have hw : algebraMap (ChartInc I t e) (ChartLoc I t e p) (s : ChartInc I t e) * w = 1 := by
    rw [← hs, ← algebraMap_tower, ← map_mul, IsLocalization.mul_mk'_eq_mk'_of_mul, mul_one,
      IsLocalization.mk'_self, map_one]
  have hz : IsLocalization.mk' (ChartLoc I t e p) (π y) s =
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (π y) * w := by
    rw [IsLocalization.mk'_eq_iff_eq_mul, mul_assoc, mul_comm w, hw, mul_one]
  show IsLocalization.mk' (ChartLoc I t e p) (π y) s ∈ A
  rw [hz]
  exact mul_mem (hSig y) (Subalgebra.algebraMap_mem A _)

end Chart

/- English proof (translation)
Rewrite using `[eval_map]`. Simplify using `only [firstGroup, specFirst]`. Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a`. Rewrite using `[aeval_C, bind₁_C_right, MvPolynomial.algebraMap_apply, eval₂_C, MvPolynomial.algebraMap_eq]`.

Consider the case `add a b ha hb`. Rewrite using `[map_add, map_add, eval₂_add, ha, hb, map_add]`. Consider the case `mul_X a ij ha`. Rewrite using `[map_mul, map_mul, eval₂_mul, ha, map_mul, aeval_X, bind₁_X_right]`. Use `congr 1`.

Take `⟨i, m⟩` from `ij`. Consider the cases of `i using Fin.cases with`. Consider the case `zero => simp [specFirstVar, algebraMap_localization_C]`. Consider the case `succ i => simp [specFirstVar]`.
-/
theorem eval_map_firstGroup {F : Type} [Field F] {n e : ℕ} (p : Ideal (MvPolynomial (Fin e × Fin n) F))
    [p.IsPrime] (f : MvPolynomial (Fin (e + 1) × Fin n) F) (u : Fin n → F) :
    eval (fun m => algebraMap F (Localization.AtPrime p) (u m))
        (map (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) (firstGroup f)) =
      algebraMap _ (Localization.AtPrime p) (specFirst f u) := by
  rw [eval_map]
  simp only [firstGroup, specFirst]
  induction f using MvPolynomial.induction_on with
  | C a =>
    rw [aeval_C, bind₁_C_right, MvPolynomial.algebraMap_apply, eval₂_C, MvPolynomial.algebraMap_eq]
  | add a b ha hb =>
    rw [map_add, map_add, eval₂_add, ha, hb, map_add]
  | mul_X a ij ha =>
    rw [map_mul, map_mul, eval₂_mul, ha, map_mul, aeval_X, bind₁_X_right]
    congr 1
    obtain ⟨i, m⟩ := ij
    cases i using Fin.cases with
    | zero => simp [specFirstVar, algebraMap_localization_C]
    | succ i => simp [specFirstVar]

end ChartNormAlgClosed

open ChartNormAlgClosed in

/- English proof (translation)
Introduce `F _ _ n e I f t p _ hI hf hp hft u`. Establish `htI : linForm t ∉ I`. Introduce `h`. Establish `hmem` using `h₂ F n e I I f t hf le_rfl h`. Rewrite `hmem` using `[h₁ F n e I f hI hf, Ideal.mem_bot]`.

Conclude with `hft (hmem ▸ p.zero_mem)`. Take `⟨hdom, hinj, -⟩` from `h₅ F n e I f t p hI hf htI`. Establish `: Module.Finite (Localization.AtPrime p) (ChartLoc I t e p)` using `h₄ F n e I f t p hI hf hft`. Establish `: IsPrincipalIdealRing (Localization.AtPrime p)`. Break down `hp with rfl | ⟨q, hq, rfl⟩` into its components or cases.

Establish `hfield : IsField (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F)))`. Rewrite using `[IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_bot]`. Set `` to `hfield.toField`. Use `infer_instance`. Use `h₃ _ q _ hq rfl infer_instance` as an intermediate fact.

Establish `: Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p)`. Rewrite using `[Module.isTorsionFree_iff_algebraMap_injective]`. Conclude with `hinj`. Establish `: Module.Free (Localization.AtPrime p) (ChartLoc I t e p)` using `Module.free_of_finite_type_torsion_free'`. Establish `hsum : ∑ m, algebraMap F (Localization.AtPrime p) (t m) • algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) = 1`.

Rewrite using `[← chartLin_eq_sum, chartLin_self, map_one]`. Establish `hcomp : (algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) = (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)).comp (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p))` using `RingHom.ext fun x => (algebraMap_tower I t p x).symm`. Establish `hdvd` using `map_dvd (MvPolynomial.map (algebraMap (ChartInc I t e) (ChartLoc I t e p))) (h₇ F n e I f t hI hf htI)`. Simplify using `only [map_sum, map_mul, map_X, map_C, map_map, hcomp] at hdvd`. Rewrite `hdvd` using `[← map_map]`.

Establish `: Infinite F` using `IsAlgClosed.instInfinite`. Establish `: Infinite (Localization.AtPrime p)` using `Infinite.of_injective _ (algebraMap F (Localization.AtPrime p)).injective`. Establish `key` using `h₈ (Localization.AtPrime p) (ChartLoc I t e p) n _ _ _ ?sep (adjoin_eq_top I t p) hsum (h₆ F n e I f p hI hf) hdvd (fun m => algebraMap F (Localization.AtPrime p) (u m))`. Use `case sep =>`. Set `_` to `FractionRing.liftAlgebra (Localization.AtPrime p) (FractionRing (ChartLoc I t e p))`.

Conclude with `@h₉ F _ _ n e I f t p _ _ _ _ _ OreLocalization.instAlgebra Localization.isLocalization _ Localization.isLocalization _ _ (FractionRing.isScalarTower_liftAlgebra _ _) _ hI hf htI`. Rewrite `key` using `[eval_map_firstGroup, eval_map_firstGroup, ← chartLin_eq_sum]`. Conclude with `key`.
-/
theorem ChartNormAlgClosed.proof (h₁ : IncIdealBelow.Statement) (h₂ : SpecFirstMemIncIdeal.Statement)
    (h₃ : LocalizationPrimeDVR.Statement) (h₄ : ChartFinite.Statement) (h₅ : ChartLocDomain.Statement)
    (h₆ : ChartFirstGroupPrime.Statement) (h₇ : ChartFirstGroupDvd.Statement)
    (h₈ : NormOfDividedFormSep.Statement) (h₉ : ChartFracSeparable.Statement) :
    ChartNormAlgClosed.Statement := by
  intro F _ _ n e I f t p _ hI hf hp hft u
  have htI : linForm t ∉ I := by
    intro h
    have hmem := h₂ F n e I I f t hf le_rfl h
    rw [h₁ F n e I f hI hf, Ideal.mem_bot] at hmem
    exact hft (hmem ▸ p.zero_mem)
  obtain ⟨hdom, hinj, -⟩ := h₅ F n e I f t p hI hf htI
  have : Module.Finite (Localization.AtPrime p) (ChartLoc I t e p) := h₄ F n e I f t p hI hf hft
  have : IsPrincipalIdealRing (Localization.AtPrime p) := by
    rcases hp with rfl | ⟨q, hq, rfl⟩
    · have hfield : IsField (Localization.AtPrime (⊥ : Ideal (MvPolynomial (Fin e × Fin n) F))) := by
        rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal,
          Ideal.map_bot]
      let := hfield.toField
      infer_instance
    · have := h₃ _ q _ hq rfl
      infer_instance
  have : Module.IsTorsionFree (Localization.AtPrime p) (ChartLoc I t e p) := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]
    exact hinj
  have : Module.Free (Localization.AtPrime p) (ChartLoc I t e p) := Module.free_of_finite_type_torsion_free'
  have hsum : ∑ m, algebraMap F (Localization.AtPrime p) (t m) •
      algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartX I t e (X m)) = 1 := by
    rw [← chartLin_eq_sum, chartLin_self, map_one]
  have hcomp : (algebraMap (ChartInc I t e) (ChartLoc I t e p)).comp
      (algebraMap (MvPolynomial (Fin e × Fin n) F) (ChartInc I t e)) =
      (algebraMap (Localization.AtPrime p) (ChartLoc I t e p)).comp
        (algebraMap (MvPolynomial (Fin e × Fin n) F) (Localization.AtPrime p)) :=
    RingHom.ext fun x => (algebraMap_tower I t p x).symm
  have hdvd := map_dvd (MvPolynomial.map (algebraMap (ChartInc I t e) (ChartLoc I t e p)))
    (h₇ F n e I f t hI hf htI)
  simp only [map_sum, map_mul, map_X, map_C, map_map, hcomp] at hdvd
  rw [← map_map] at hdvd
  have : Infinite F := IsAlgClosed.instInfinite
  have : Infinite (Localization.AtPrime p) :=
    Infinite.of_injective _ (algebraMap F (Localization.AtPrime p)).injective
  have key := h₈ (Localization.AtPrime p) (ChartLoc I t e p) n _ _ _ ?sep (adjoin_eq_top I t p) hsum
    (h₆ F n e I f p hI hf) hdvd (fun m => algebraMap F (Localization.AtPrime p) (u m))
  case sep =>
    let _ := FractionRing.liftAlgebra (Localization.AtPrime p) (FractionRing (ChartLoc I t e p))
    exact @h₉ F _ _ n e I f t p _ _ _ _ _ OreLocalization.instAlgebra Localization.isLocalization _ Localization.isLocalization _ _
      (FractionRing.isScalarTower_liftAlgebra _ _) _ hI hf htI
  rw [eval_map_firstGroup, eval_map_firstGroup, ← chartLin_eq_sum] at key
  exact key

end

end GroundTheory.Heights₂.Heights
