import Formalism.SatakeDualWeyl.DefsCS

noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.UG.P

open Formalism.UG

section

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Use `first`. Consider the case `exact (v.valuedAdicCompletion_eq_valuation r).trans (v.valuation_of_algebraMap r)`. Consider the case `exact (v.valuedAdicCompletion_eq_valuation r).trans (v.valuation_of_algebraMap (K := F) r)`. Consider the case `(rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]`. Conclude with `(v.valuedAdicCompletion_eq_valuation' _).trans (v.valuation_of_algebraMap (K := F) r))`.
-/
theorem csGlobApprox_vD (v : HeightOneSpectrum (𝓞 F)) (r : 𝓞 F) :
    Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) r) = v.intValuation r := by
  first
  | exact (v.valuedAdicCompletion_eq_valuation r).trans (v.valuation_of_algebraMap r)
  | exact (v.valuedAdicCompletion_eq_valuation r).trans (v.valuation_of_algebraMap (K := F) r)
  | (rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F)]
     exact (v.valuedAdicCompletion_eq_valuation' _).trans (v.valuation_of_algebraMap (K := F) r))

/- English proof (translation)
Use `set Dv := algebraMap (𝓞 F) (v.adicCompletion F) D with hDvdef`. Establish `hDv : Dv ≠ 0` using `levelaf_algebraMap_ne_zero v D hD`. Establish `hDv0 : Valued.v Dv ≠ 0` using `(Valuation.ne_zero_iff _).2 hDv`. Establish `hDv1 : Valued.v Dv ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 (levelaf_int_mem_v v D)`. Establish `hx1 : Valued.v x ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 hx`.

Establish `ho : IsOpen ((fun y => (y - x) * Dv⁻¹) ⁻¹' ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F)))` using `(Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)`. Take `⟨f, hf⟩` from `(HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open ho ⟨x, by simp⟩`. Establish `hf' : Valued.v (algebraMap F (v.adicCompletion F) f - x) ≤ Valued.v Dv`. Establish `h` using `(Valuation.mem_integer_iff _ _).1 hf`. Simplify using `only [map_mul, map_inv₀] at h`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[inv_mul_cancel_right₀ hDv0]`. Use `_ ≤ 1 * Valued.v Dv := mul_le_mul_left h _`. Use `_ = Valued.v Dv := one_mul _`. Establish `hfv : v.valuation F f ≤ 1`.

Rewrite using `[← levelaf_valued_algebraMap]`. Rewrite using `[show algebraMap F (v.adicCompletion F) f = (algebraMap F (v.adicCompletion F) f - x) + x by ring]`. Conclude with `Valuation.map_add_le _ (hf'.trans hDv1) hx1`. Establish `hD' : v.intValuation D ≠ 0` using `by rw [← csGlobApprox_vD]; exact hDv0`. Take `⟨a, ha⟩` from `HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hfv (Units.mk0 _ hD')`.

Use `⟨a, ?_⟩` and prove the remaining obligations. Establish `h2 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) f) ≤ Valued.v Dv`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub, levelaf_valued_algebraMap, hDvdef, csGlobApprox_vD]`. Conclude with `ha.le`. Rewrite using `[show x - algebraMap (𝓞 F) (v.adicCompletion F) a = -(algebraMap F (v.adicCompletion F) f - x) + -(algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) f) by ring]`.

Conclude with `Valuation.map_add_le _ (by rw [Valuation.map_neg]; exact hf') (by rw [Valuation.map_neg]; exact h2)`.
-/
theorem csGlobApprox_local (v : HeightOneSpectrum (𝓞 F)) (D : 𝓞 F) (hD : D ≠ 0)
    (x : v.adicCompletion F) (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ r : 𝓞 F, Valued.v (x - algebraMap (𝓞 F) (v.adicCompletion F) r) ≤
      Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) D) := by
  set Dv := algebraMap (𝓞 F) (v.adicCompletion F) D with hDvdef
  have hDv : Dv ≠ 0 := levelaf_algebraMap_ne_zero v D hD
  have hDv0 : Valued.v Dv ≠ 0 := (Valuation.ne_zero_iff _).2 hDv
  have hDv1 : Valued.v Dv ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 (levelaf_int_mem_v v D)
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (K := F) (v := v)).1 hx
  have ho : IsOpen ((fun y => (y - x) * Dv⁻¹) ⁻¹'
      ((Valued.v : Valuation (v.adicCompletion F) _).integer : Set (v.adicCompletion F))) :=
    (Valued.isOpen_integer _).preimage ((continuous_id.sub continuous_const).mul continuous_const)
  obtain ⟨f, hf⟩ := (HeightOneSpectrum.denseRange_algebraMap F v).exists_mem_open ho
    ⟨x, by simp⟩
  have hf' : Valued.v (algebraMap F (v.adicCompletion F) f - x) ≤ Valued.v Dv := by
    have h := (Valuation.mem_integer_iff _ _).1 hf
    simp only [map_mul, map_inv₀] at h
    calc Valued.v (algebraMap F (v.adicCompletion F) f - x)
        = Valued.v (algebraMap F (v.adicCompletion F) f - x) * (Valued.v Dv)⁻¹ * Valued.v Dv := by
          rw [inv_mul_cancel_right₀ hDv0]
      _ ≤ 1 * Valued.v Dv := mul_le_mul_left h _
      _ = Valued.v Dv := one_mul _
  have hfv : v.valuation F f ≤ 1 := by
    rw [← levelaf_valued_algebraMap]
    rw [show algebraMap F (v.adicCompletion F) f = (algebraMap F (v.adicCompletion F) f - x) + x by
      ring]
    exact Valuation.map_add_le _ (hf'.trans hDv1) hx1
  have hD' : v.intValuation D ≠ 0 := by rw [← csGlobApprox_vD]; exact hDv0
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hfv (Units.mk0 _ hD')
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) f)
      ≤ Valued.v Dv := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F), ← map_sub,
      levelaf_valued_algebraMap, hDvdef, csGlobApprox_vD]
    exact ha.le
  rw [show x - algebraMap (𝓞 F) (v.adicCompletion F) a =
      -(algebraMap F (v.adicCompletion F) f - x) +
        -(algebraMap (𝓞 F) (v.adicCompletion F) a - algebraMap F (v.adicCompletion F) f) by ring]
  exact Valuation.map_add_le _ (by rw [Valuation.map_neg]; exact hf')
    (by rw [Valuation.map_neg]; exact h2)

end

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `hmem : z ∈ ⨅ i : ℕ, w.asIdeal ^ i` using `Submodule.mem_iInf _ |>.2 h`. Rewrite `hmem` using `[Ideal.iInf_pow_eq_bot_of_isDomain]`. Conclude with `hz ((Submodule.mem_bot _).1 hmem)`.

Conclude with `w.isPrime.ne_top`.
-/
private theorem exists_not_mem_asIdeal_pow_of_ne_zero {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (z : 𝓞 F) (hz : z ≠ 0) :
    ∃ n : ℕ, z ∉ w.asIdeal ^ n := by
  by_contra h
  push_neg at h
  have hmem : z ∈ ⨅ i : ℕ, w.asIdeal ^ i := Submodule.mem_iInf _ |>.2 h
  rw [Ideal.iInf_pow_eq_bot_of_isDomain] at hmem
  · exact hz ((Submodule.mem_bot _).1 hmem)
  · exact w.isPrime.ne_top

/- English proof (translation)
The claim follows from `lt_of_le_of_lt ((w.intValuation_le_pow_iff_mem z n).2 hz) (not_le.1 fun h => hDn ((w.intValuation_le_pow_iff_mem D n).1 h))`.
-/
private theorem intValuation_lt_of_mem_pow_of_not_mem_pow {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) {z D : 𝓞 F} {n : ℕ}
    (hDn : D ∉ w.asIdeal ^ n) (hz : z ∈ w.asIdeal ^ n) : w.intValuation z < w.intValuation D :=
  lt_of_le_of_lt ((w.intValuation_le_pow_iff_mem z n).2 hz)
    (not_le.1 fun h => hDn ((w.intValuation_le_pow_iff_mem D n).1 h))

/- English proof (translation)
Use `first`. Consider the case `exact w.valuedAdicCompletion_eq_valuation' k`. Consider the case `rfl`. Consider the case `simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']`.
-/
private theorem valued_v_algebraMap_adicCompletion {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (k : F) :
    Valued.v (algebraMap F (w.adicCompletion F) k) = w.valuation F k := by
  first
  | exact w.valuedAdicCompletion_eq_valuation' k
  | rfl
  | simp [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/- English proof (translation)
Introduce `F _ _ D hD a ha`. Establish `ha' : ∀ w : HeightOneSpectrum (𝓞 F), a w ∈ w.adicCompletionIntegers F` using `ha`. Establish `hfin : {w : HeightOneSpectrum (𝓞 F) | D ∈ w.asIdeal}.Finite`. Establish `h` using `Ideal.finite_factors (I := Ideal.span {D}) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hD)`. Simplify `h` using `only [Ideal.dvd_span_singleton]`.

Use `choose r hr using fun w : HeightOneSpectrum (𝓞 F) => csGlobApprox_local w D hD (a w) (ha' w)`. Use `choose e he using fun w : HeightOneSpectrum (𝓞 F) => exists_not_mem_asIdeal_pow_of_ne_zero w D hD`. Take `⟨r0, hr0⟩` from `IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset) (fun w => w.asIdeal) e (fun w _ => w.prime) (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun w => r w.1)`. Establish `hγ : ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation D ≠ 0` using `fun w => (lt_of_le_of_lt zero_le' (intValuation_lt_of_mem_pow_of_not_mem_pow w (he w) (Submodule.zero_mem _))).ne'`. Establish `hbound : ∀ w : HeightOneSpectrum (𝓞 F), Valued.v (a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) ≤ w.intValuation D`.

Introduce `w`. Distinguish the cases in `hw : D ∈ w.asIdeal`. Establish `hmem` using `hr0 w (hfin.mem_toFinset.2 hw)`. Establish `h1` using `hr w`. Rewrite `h1` using `[csGlobApprox_vD]`.

Establish `h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) (r w) - algebraMap (𝓞 F) (w.adicCompletion F) r0) ≤ w.intValuation D`. Rewrite using `[Valuation.map_sub_swap, ← map_sub, csGlobApprox_vD]`. Conclude with `(intValuation_lt_of_mem_pow_of_not_mem_pow w (he w) hmem).le`. Rewrite using `[← sub_add_sub_cancel (a w) (algebraMap (𝓞 F) (w.adicCompletion F) (r w))]`. Conclude with `Valuation.map_add_le _ h1 h2`.

Establish `h1 : w.intValuation D = 1`. Use `le_antisymm (w.intValuation_le_one D) ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Use `first`.

Consider the case `exact hw ((w.intValuation_lt_one_iff_mem D).1 hlt)`. Consider the case `exact hw (Ideal.dvd_span_singleton.1 ((w.intValuation_lt_one_iff_dvd D).1 hlt))`. Rewrite using `[h1]`. Use `le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)` and prove the remaining obligations. Conclude with `ha' w`.

Rewrite using `[csGlobApprox_vD]`. Conclude with `w.intValuation_le_one r0`. Establish `hd : algebraMap (𝓞 F) F D ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD`. Establish `hsc : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) D = algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D)` using `by first`. Consider the case `exact IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D`.

Consider the case `rfl`. Establish `hunit : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) D * algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D)⁻¹ = 1`. Rewrite using `[hsc, ← map_mul, mul_inv_cancel₀ hd, map_one]`. Take `⟨Y, hY⟩ : ∃ Y : FiniteAdeleRing (𝓞 F) F, Y = (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r0) * algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D)⁻¹` from `⟨_, rfl⟩`. Use `⟨r0, Y, (fun w => ?_ : ∀ w : HeightOneSpectrum (𝓞 F), Y w ∈ w.adicCompletionIntegers F), ?_⟩` and prove the remaining obligations.

Establish `hcoord : Y w = (a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) * algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹`. Rewrite using `[hY]`. Use `first`. Consider the case `rfl`. Consider the case `simp`.

Rewrite using `[hcoord]`. Establish `hle : Valued.v ((a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) * algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹) ≤ 1`. Rewrite using `[map_mul, valued_v_algebraMap_adicCompletion, map_inv₀, w.valuation_of_algebraMap]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `exact mul_le_mul_right (hbound w) _`.

Consider the case `exact mul_le_mul_of_nonneg_right (hbound w) zero_le'`. Consider the case `(gcongr; exact hbound w)`. Use `_ = 1 := mul_inv_cancel₀ (hγ w)`. Conclude with `hle`. Rewrite using `[hY]`.

Take the linear combination `(algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r0 - a) * hunit`.
-/
theorem csGlob_intAdApprox : Formalism.UG.CS.IntAdApprox := by
  intro F _ _ D hD a ha
  classical
  have ha' : ∀ w : HeightOneSpectrum (𝓞 F), a w ∈ w.adicCompletionIntegers F := ha
  have hfin : {w : HeightOneSpectrum (𝓞 F) | D ∈ w.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {D})
      (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hD)
    simpa only [Ideal.dvd_span_singleton] using h
  choose r hr using fun w : HeightOneSpectrum (𝓞 F) => csGlobApprox_local w D hD (a w) (ha' w)
  choose e he using fun w : HeightOneSpectrum (𝓞 F) => exists_not_mem_asIdeal_pow_of_ne_zero w D hD
  obtain ⟨r0, hr0⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun w => w.asIdeal) e (fun w _ => w.prime)
    (fun i _ j _ hij h => hij (HeightOneSpectrum.ext h)) (fun w => r w.1)
  have hγ : ∀ w : HeightOneSpectrum (𝓞 F), w.intValuation D ≠ 0 := fun w =>
    (lt_of_le_of_lt zero_le' (intValuation_lt_of_mem_pow_of_not_mem_pow w (he w) (Submodule.zero_mem _))).ne'
  have hbound : ∀ w : HeightOneSpectrum (𝓞 F),
      Valued.v (a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) ≤ w.intValuation D := by
    intro w
    by_cases hw : D ∈ w.asIdeal
    · have hmem := hr0 w (hfin.mem_toFinset.2 hw)
      have h1 := hr w
      rw [csGlobApprox_vD] at h1
      have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) (r w) -
          algebraMap (𝓞 F) (w.adicCompletion F) r0) ≤ w.intValuation D := by
        rw [Valuation.map_sub_swap, ← map_sub, csGlobApprox_vD]
        exact (intValuation_lt_of_mem_pow_of_not_mem_pow w (he w) hmem).le
      rw [← sub_add_sub_cancel (a w) (algebraMap (𝓞 F) (w.adicCompletion F) (r w))]
      exact Valuation.map_add_le _ h1 h2
    · have h1 : w.intValuation D = 1 := by
        refine le_antisymm (w.intValuation_le_one D) ?_
        by_contra hlt
        push_neg at hlt
        first
        | exact hw ((w.intValuation_lt_one_iff_mem D).1 hlt)
        | exact hw (Ideal.dvd_span_singleton.1 ((w.intValuation_lt_one_iff_dvd D).1 hlt))
      rw [h1]
      refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
      · exact ha' w
      · rw [csGlobApprox_vD]
        exact w.intValuation_le_one r0
  have hd : algebraMap (𝓞 F) F D ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hD
  have hsc : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) D =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D) := by
    first
    | exact IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) D
    | rfl
  have hunit : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) D *
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D)⁻¹ = 1 := by
    rw [hsc, ← map_mul, mul_inv_cancel₀ hd, map_one]
  obtain ⟨Y, hY⟩ : ∃ Y : FiniteAdeleRing (𝓞 F) F, Y =
      (a - algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r0) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F D)⁻¹ := ⟨_, rfl⟩
  refine ⟨r0, Y, (fun w => ?_ : ∀ w : HeightOneSpectrum (𝓞 F), Y w ∈ w.adicCompletionIntegers F), ?_⟩
  · have hcoord : Y w = (a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) *
        algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹ := by
      rw [hY]
      first
      | rfl
      | simp
    rw [hcoord]
    have hle : Valued.v ((a w - algebraMap (𝓞 F) (w.adicCompletion F) r0) *
        algebraMap F (w.adicCompletion F) (algebraMap (𝓞 F) F D)⁻¹) ≤ 1 := by
      rw [map_mul, valued_v_algebraMap_adicCompletion, map_inv₀, w.valuation_of_algebraMap]
      calc _ ≤ w.intValuation D * (w.intValuation D)⁻¹ := by
            first
            | exact mul_le_mul_right (hbound w) _
            | exact mul_le_mul_of_nonneg_right (hbound w) zero_le'
            | (gcongr; exact hbound w)
        _ = 1 := mul_inv_cancel₀ (hγ w)
    exact hle
  · rw [hY]
    linear_combination (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r0 - a) * hunit

end Formalism.UG.P
