import Formalism.SatakeDualWeyl.DefsCS

noncomputable section
namespace Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero

section CsApprox

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]`. Use `first`. Consider the case `(rw [valuedAdicCompletion_eq_valuation' v]; exact valuation_of_algebraMap v r)`. Consider the case `simp [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]`. Consider the case `(erw [valuedAdicCompletion_eq_valuation']; exact valuation_of_algebraMap v r)`.
-/
theorem csApprox_val_int (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
  rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
  first
  | (rw [valuedAdicCompletion_eq_valuation' v]; exact valuation_of_algebraMap v r)
  | simp [valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  | (erw [valuedAdicCompletion_eq_valuation']; exact valuation_of_algebraMap v r)

/- English proof (translation)
Use `set c := algebraMap (𝓞 F) (v.adicCompletion F) D with hcdef`. Establish `hc : c ≠ 0` using `levelaf_algebraMap_ne_zero v D hD`. Establish `hrc : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).restrict c ≠ 0` using `(Valuation.ne_zero_iff _).2 hc`. Establish `hs : {y : v.adicCompletion F | Valued.v (y - x) < Valued.v c} ∈ nhds x`. Use `Valued.mem_nhds.2 ⟨Units.mk0 _ hrc, fun y hy => ?_⟩` and prove the remaining obligations.

Simplify using `only [Set.mem_ofPred_eq, Units.val_mk0] at hy ⊢`. Conclude with `lt_of_not_ge fun h => (not_le.2 hy) ((Valuation.restrict_le_iff _).2 h)`. Take `⟨b, hb⟩` from `(denseRange_algebraMap (K := F) v).mem_nhds hs`. Simplify using `only [Set.mem_ofPred_eq] at hb`. Establish `hcv : Valued.v c = v.intValuation D` using `csApprox_val_int v D`.

Rewrite `hb` using `[hcv]`. Establish `hb1 : v.valuation F b ≤ 1`. Rewrite using `[← levelaf_valued_algebraMap]`. Establish `e : algebraMap F (v.adicCompletion F) b = (algebraMap F (v.adicCompletion F) b - x) + x`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Valuation.map_add_le _ (hb.le.trans (v.intValuation_le_one D)) hx`. Take `⟨s, hs⟩` from `exists_valuation_sub_lt_of_integer v hb1 (Units.mk0 (v.intValuation D) (v.intValuation_ne_zero D hD))`. Simplify using `only [Units.val_mk0] at hs`. Use `⟨s, ?_⟩` and prove the remaining obligations.

Establish `hs' : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b) < v.intValuation D`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub, levelaf_valued_algebraMap]`. Conclude with `hs`. Establish `e2 : x - algebraMap (𝓞 F) (v.adicCompletion F) s = -(algebraMap F (v.adicCompletion F) b - x) + -(algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b)`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e2]`. Use `Valuation.map_add_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_neg]`. Conclude with `hb`. Rewrite using `[Valuation.map_neg]`.

Conclude with `hs'`.
-/
theorem csApprox_local (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ s : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) s) < v.intValuation D := by
  set c := algebraMap (𝓞 F) (v.adicCompletion F) D with hcdef
  have hc : c ≠ 0 := levelaf_algebraMap_ne_zero v D hD
  have hrc : (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).restrict c ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hc
  have hs : {y : v.adicCompletion F | Valued.v (y - x) < Valued.v c} ∈ nhds x := by
    refine Valued.mem_nhds.2 ⟨Units.mk0 _ hrc, fun y hy => ?_⟩
    simp only [Set.mem_ofPred_eq, Units.val_mk0] at hy ⊢
    exact lt_of_not_ge fun h => (not_le.2 hy) ((Valuation.restrict_le_iff _).2 h)
  obtain ⟨b, hb⟩ := (denseRange_algebraMap (K := F) v).mem_nhds hs
  simp only [Set.mem_ofPred_eq] at hb
  have hcv : Valued.v c = v.intValuation D := csApprox_val_int v D
  rw [hcv] at hb
  have hb1 : v.valuation F b ≤ 1 := by
    rw [← levelaf_valued_algebraMap]
    have e : algebraMap F (v.adicCompletion F) b = (algebraMap F (v.adicCompletion F) b - x) + x := by
      ring
    rw [e]
    exact Valuation.map_add_le _ (hb.le.trans (v.intValuation_le_one D)) hx
  obtain ⟨s, hs⟩ := exists_valuation_sub_lt_of_integer v hb1
    (Units.mk0 (v.intValuation D) (v.intValuation_ne_zero D hD))
  simp only [Units.val_mk0] at hs
  refine ⟨s, ?_⟩
  have hs' : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b)
      < v.intValuation D := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub,
      levelaf_valued_algebraMap]
    exact hs
  have e2 : x - algebraMap (𝓞 F) (v.adicCompletion F) s =
      -(algebraMap F (v.adicCompletion F) b - x) +
        -(algebraMap (𝓞 F) (v.adicCompletion F) s - algebraMap F (v.adicCompletion F) b) := by
    ring
  rw [e2]
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [Valuation.map_neg]; exact hb
  · rw [Valuation.map_neg]; exact hs'

/- English proof (translation)
Establish `hP` using `levelaf_finite_places D hD`. Use `choose s hs using fun v : HeightOneSpectrum (𝓞 F) => csApprox_local v D hD (a v) (ha v)`. Take `⟨r, hr⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := hP.toFinset) (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal) (fun v => multiplicity v.asIdeal (Ideal.span {D})) (fun v _ => v.prime) (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => s v)`. Use `⟨r, fun v => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hv : v ∈ hP.toFinset`.

Establish `h1` using `(v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)`. Rewrite `h1` using `[← v.intValuation_eq_exp_neg_multiplicity hD]`. Establish `e1 : a v - algebraMap (𝓞 F) (v.adicCompletion F) r = (a v - algebraMap (𝓞 F) (v.adicCompletion F) (s v)) + -(algebraMap (𝓞 F) (v.adicCompletion F) (r - s v))`. Rewrite using `[map_sub]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, csApprox_val_int]`. Use `Valuation.map_add_le _ (hs v).le ?_` and prove the remaining obligations. Rewrite using `[Valuation.map_neg, csApprox_val_int]`. Conclude with `h1`. Establish `hv' : ¬ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1` using `by simpa using hv`.

Establish `h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = 1` using `le_antisymm ((mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v v D)) (not_lt.1 hv')`. Rewrite using `[h1]`. Conclude with `(mem_adicCompletionIntegers _ _ _).1 (sub_mem (ha v) (levelaf_int_mem_v v r))`.
-/
theorem csApprox_global (D : 𝓞 F) (hD : D ≠ 0) (a : FiniteAdeleRing (𝓞 F) F) (ha : a ∈ intAd F) :
    ∃ r : 𝓞 F, ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
        Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  classical
  have hP := levelaf_finite_places D hD
  choose s hs using fun v : HeightOneSpectrum (𝓞 F) => csApprox_local v D hD (a v) (ha v)
  obtain ⟨r, hr⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hP.toFinset)
    (fun v : HeightOneSpectrum (𝓞 F) => v.asIdeal)
    (fun v => multiplicity v.asIdeal (Ideal.span {D})) (fun v _ => v.prime)
    (fun v _ w _ hvw h => hvw (HeightOneSpectrum.ext h)) (fun v => s v)
  refine ⟨r, fun v => ?_⟩
  by_cases hv : v ∈ hP.toFinset
  · have h1 := (v.intValuation_le_pow_iff_mem _ _).2 (hr v hv)
    rw [← v.intValuation_eq_exp_neg_multiplicity hD] at h1
    have e1 : a v - algebraMap (𝓞 F) (v.adicCompletion F) r =
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) (s v)) +
          -(algebraMap (𝓞 F) (v.adicCompletion F) (r - s v)) := by
      rw [map_sub]; ring
    rw [e1, csApprox_val_int]
    refine Valuation.map_add_le _ (hs v).le ?_
    rw [Valuation.map_neg, csApprox_val_int]
    exact h1
  · have hv' : ¬ Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) < 1 := by simpa using hv
    have h1 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) = 1 :=
      le_antisymm ((mem_adicCompletionIntegers _ _ _).1 (levelaf_int_mem_v v D)) (not_lt.1 hv')
    rw [h1]
    exact (mem_adicCompletionIntegers _ _ _).1 (sub_mem (ha v) (levelaf_int_mem_v v r))

end CsApprox

/- English proof (translation)
Introduce `F _ _ D hD a ha`. Take `⟨r, hle⟩` from `csApprox_global D hD a ha`. Use `set y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F D)⁻¹ * (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) with hy`. Use `⟨r, y, fun v => ?_, ?_⟩` and prove the remaining obligations. Use `show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ * (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ∈ _`.

Establish `hne : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) ≠ 0` using `(Valuation.ne_zero_iff _).2 (levelaf_algebraMap_ne_zero v D hD)`. Rewrite using `[mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀, ← IsScalarTower.algebraMap_apply]`. Combine the equalities or inequalities in the displayed calculation. Establish `hD' : algebraMap (𝓞 F) F D ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD`. Rewrite using `[hy, IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hD', map_one, one_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem integral_adele_approximation_holds : Formalism.UG.CS.IntAdApprox := by
  intro F _ _ D hD a ha
  obtain ⟨r, hle⟩ := csApprox_global D hD a ha
  set y : FiniteAdeleRing (𝓞 F) F := algebraMap F _ (algebraMap (𝓞 F) F D)⁻¹ *
    (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) with hy
  refine ⟨r, y, fun v => ?_, ?_⟩
  · show algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ *
        (a v - algebraMap (𝓞 F) (v.adicCompletion F) r) ∈ _
    have hne : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (levelaf_algebraMap_ne_zero v D hD)
    rw [mem_adicCompletionIntegers, Valuation.map_mul, map_inv₀, map_inv₀,
      ← IsScalarTower.algebraMap_apply]
    calc _ ≤ (Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D))⁻¹ *
          Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := mul_le_mul_right (hle v) _
      _ = 1 := inv_mul_cancel₀ hne
  · have hD' : algebraMap (𝓞 F) F D ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
    rw [hy, IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D, ← mul_assoc,
      ← map_mul, mul_inv_cancel₀ hD', map_one, one_mul]
    ring

end Formalism.UG.P
