import Mathlib
import Formalism.LocalToGlobal.KernelLattices.MuProd
import Formalism.LocalToGlobal.UnitaryNorms.CharProd

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.L2.Col Formalism.L2.Host

section Loc

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Distinguish the cases in `h0 : x = 0`. Rewrite using `[h0]`. Conclude with `zero_le`. Rewrite `h`, the goal using `[← WithZero.exp_log h0]`. Rewrite `h` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
theorem hk_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : x = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

/- English proof (translation)
Establish `e : a = 1 + (a - 1)` using `by ring`. Rewrite using `[e]`. Establish `h1 : P.valuation E (a - 1) < P.valuation E (1 : E)` using `by rw [map_one]; exact h`. Rewrite using `[Valuation.map_add_eq_of_lt_left _ h1, map_one]`.
-/
theorem hk_val_one {P : HeightOneSpectrum (𝓞 E)} {a : E} (h : OneAt P a) : P.valuation E a = 1 := by
  have e : a = 1 + (a - 1) := by ring
  rw [e]
  have h1 : P.valuation E (a - 1) < P.valuation E (1 : E) := by rw [map_one]; exact h
  rw [Valuation.map_add_eq_of_lt_left _ h1, map_one]

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (a : E)`.
-/
theorem hk_valued (P : HeightOneSpectrum (𝓞 E)) (a : Eˣ) :
    Valued.v ((atFin P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) = P.valuation E (a : E) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (a : E)

/- English proof (translation)
Establish `e : ((atFin P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1 = (((a : E) - 1 : E) : P.adicCompletion E)` using `by show algebraMap E (P.adicCompletion E) (a : E) - 1 = algebraMap E (P.adicCompletion E) ((a : E) - 1)`. Rewrite using `[map_sub, map_one]`. Rewrite using `[e]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P ((a : E) - 1)`.
-/
theorem hk_valued_sub (P : HeightOneSpectrum (𝓞 E)) (a : Eˣ) :
    Valued.v (((atFin P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1) = P.valuation E ((a : E) - 1) := by
  have e : ((atFin P a : (P.adicCompletion E)ˣ) : P.adicCompletion E) - 1 = (((a : E) - 1 : E) : P.adicCompletion E) := by
    show algebraMap E (P.adicCompletion E) (a : E) - 1 = algebraMap E (P.adicCompletion E) ((a : E) - 1)
    rw [map_sub, map_one]
  rw [e]
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P ((a : E) - 1)

/- English proof (translation)
Use `h (atFin P a) ?_ ?_` and prove the remaining obligations. Use `show Valued.v _ = 1`. Rewrite using `[hk_valued, hk_val_one ha]`. Rewrite using `[hk_valued_sub]`. Conclude with `hk_le_exp ha`.
-/
theorem hk_tame (χ : HChar E) {P : HeightOneSpectrum (𝓞 E)} (h : χ.TameAt P) (a : Eˣ) (ha : OneAt P (a : E)) : χ.locK P a = 1 := by
  refine h (atFin P a) ?_ ?_
  · show Valued.v _ = 1
    rw [hk_valued, hk_val_one ha]
  · rw [hk_valued_sub]
    exact hk_le_exp ha

/- English proof (translation)
Use `h (atFin P a) ?_` and prove the remaining obligations. Use `show Valued.v _ = 1`. Rewrite using `[hk_valued, ha]`.
-/
theorem hk_unr (χ : HChar E) {P : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt P) (a : Eˣ) (ha : P.valuation E (a : E) = 1) : χ.locK P a = 1 := by
  refine h (atFin P a) ?_
  show Valued.v _ = 1
  rw [hk_valued, ha]

/- English proof (translation)
Use `χ.val_eq h (atFin P a) ?_` and prove the remaining obligations. Use `show Valued.v _ = _`. Rewrite using `[hk_valued, ha]`.
-/
theorem hk_unif (χ : HChar E) {P : HeightOneSpectrum (𝓞 E)} (h : χ.UnrAt P) (a : Eˣ) (ha : P.valuation E (a : E) = WithZero.exp (-1 : ℤ)) :
    χ.locK P a = χ.val P := by
  refine χ.val_eq h (atFin P a) ?_
  show Valued.v _ = _
  rw [hk_valued, ha]

/- English proof (translation)
Introduce `_ _ _ χ _` and use `⟨fun h a ha => hk_tame χ h a ha, fun h a ha => hk_unr χ h a ha, fun h a ha => hk_unif χ h a ha⟩`.
-/
theorem hecke_character_local_behaviour : HLoc := fun _ _ _ χ _ =>
  ⟨fun h a ha => hk_tame χ h a ha, fun h a ha => hk_unr χ h a ha, fun h a ha => hk_unif χ h a ha⟩

end Loc

section Sys

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Unfold `aboveF`. Rewrite using `[Set.Finite.mem_toFinset, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[← h]`.

Both sides reduce to the same expression. Introduce `h`. Conclude with `HeightOneSpectrum.ext h`.
-/
theorem hk_mem_above (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) :
    P ∈ aboveF (L := E) F v ↔ P.asIdeal.under (𝓞 F) = v.asIdeal := by
  unfold aboveF
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  constructor
  · intro h; rw [← h]; rfl
  · intro h; exact HeightOneSpectrum.ext h

/- English proof (translation)
Unfold `lamH`. Rewrite using `[MonoidHom.finsetProd_apply]`.
-/
theorem hk_lamH (χ : HChar E) (v : HeightOneSpectrum (𝓞 F)) (a : Eˣ) :
    lamH (F := F) χ v a = ∏ P ∈ aboveF (L := E) F v, χ.locK P a := by
  unfold lamH
  rw [MonoidHom.finsetProd_apply]

/- English proof (translation)
Introduce `F E _ _ _ _ _ χ Rm ht hF hu`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `v a ha`. Rewrite using `[hk_lamH]`. Conclude with `Finset.prod_eq_one fun P hP => hk_tame χ (ht P) a (ha P ((hk_mem_above v P).1 hP))`.

Introduce `v k`. Rewrite using `[hk_lamH]`. Establish `h` using `hF.1 v k`. Unfold `HChar.resFin at h`. Rewrite `h` using `[MonoidHom.finsetProd_apply]`.

Conclude with `h`. Introduce `v hv a ha`. Rewrite using `[hk_lamH]`. Conclude with `Finset.prod_eq_one fun P hP => hk_unr χ (hu v hv P ((hk_mem_above v P).1 hP)) a (ha P ((hk_mem_above v P).1 hP))`.
-/
theorem hecke_character_compatible_system : HSys := by
  intro F E _ _ _ _ _ χ Rm ht hF hu
  refine ⟨?_, ?_, ?_⟩
  · intro v a ha
    rw [hk_lamH]
    exact Finset.prod_eq_one fun P hP => hk_tame χ (ht P) a (ha P ((hk_mem_above v P).1 hP))
  · intro v k
    rw [hk_lamH]
    have h := hF.1 v k
    unfold HChar.resFin at h
    rw [MonoidHom.finsetProd_apply] at h
    exact h
  · intro v hv a ha
    rw [hk_lamH]
    exact Finset.prod_eq_one fun P hP =>
      hk_unr χ (hu v hv P ((hk_mem_above v P).1 hP)) a (ha P ((hk_mem_above v P).1 hP))

/- English proof (translation)
Introduce `F E _ _ _ _ _ χ ht v P hP b hb`. Rewrite using `[hk_lamH]`. Use `Finset.prod_eq_single P ?_ ?_` and prove the remaining obligations. Introduce `P' hP' hne`. Conclude with `hk_tame χ (ht P') b (hb P' hne ((hk_mem_above v P').1 hP'))`.

Introduce `h`. Conclude with `absurd ((hk_mem_above v P).2 hP) h`.
-/
theorem hecke_character_evaluation : HEval := by
  intro F E _ _ _ _ _ χ ht v P hP b hb
  rw [hk_lamH]
  refine Finset.prod_eq_single P ?_ ?_
  · intro P' hP' hne
    exact hk_tame χ (ht P') b (hb P' hne ((hk_mem_above v P').1 hP'))
  · intro h
    exact absurd ((hk_mem_above v P).2 hP) h

end Sys

section Prod

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Introduce `F E _ _ _ _ _ χ S hS x`. Establish `hfin : {P : HeightOneSpectrum (𝓞 E) | ¬ P.valuation E (x : E) = 1}.Finite`. Establish `h` using `Filter.eventually_cofinite.1 (valued_comp_eventually E (diagUnits E x))`. Simplify `h` using `only [diag_comp]`. Use `set T0 : Finset (HeightOneSpectrum (𝓞 E)) := S ∪ hfin.toFinset with hT0`.

Establish `hval : ∀ P, P ∉ T0 → P.valuation E (x : E) = 1`. Introduce `P hP`. Assume the negation of the conclusion as `h`. Conclude with `hP (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))`. Establish `hone : ∀ P, P ∉ T0 → χ.locK P x = 1` using `fun P hP => hk_unr χ (hS P fun h => hP (Finset.mem_union_left _ h)) x (hval P hP)`.

Establish `hmain : χ.inf x * ∏ P ∈ T0, χ.locK P x = 1`. Establish `h` using `χ.productRule T0 (fun P hP => hS P fun h => hP (Finset.mem_union_left _ h)) x`. Establish `h2 : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ T0), χ.val v ^ ordF v x) = 1`. Use `finprod_eq_one_of_forall_eq_one fun P => ?_` and prove the remaining obligations. Rewrite using `[finprod_eq_if]`.

Use `split_ifs with hP`. Both sides reduce to the same expression. Establish `h0 : ordF P x = 0`. Unfold `ordF`. Rewrite using `[hval P hP, WithZero.log_one, neg_zero]`.

Rewrite using `[h0, zpow_zero]`. Rewrite `h` using `[h2, mul_one]`. Conclude with `h`. Use `set T : Finset (HeightOneSpectrum (𝓞 F)) := T0.image (fun P => P.under (𝓞 F)) with hT`. Establish `hsupp : ∀ v, v ∉ T → lamH (F` using `F) χ v x = 1 := by`.

Introduce `v hv`. Rewrite using `[hk_lamH]`. Use `Finset.prod_eq_one fun P hP => hone P fun hPT => hv ?_` and prove the remaining obligations. Rewrite using `[hT, Finset.mem_image]`. Conclude with `⟨P, hPT, HeightOneSpectrum.ext ((hk_mem_above v P).1 hP)⟩`.

Establish `hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => lamH (F` using `F) χ v x) ⊆ ↑T := by`. Introduce `v hv`. Assume the negation of the conclusion as `h`. Conclude with `hv (hsupp v h)`. Use `⟨T.finite_toSet.subset hsub, ?_⟩` and prove the remaining obligations.

Rewrite using `[finprod_eq_prod_of_mulSupport_subset _ hsub]`. Establish `e : ∏ v ∈ T, lamH (F` using `F) χ v x = ∏ P ∈ T0, χ.locK P x := by`. Rewrite using `[← Finset.prod_fiberwise_of_maps_to (s := T0) (t := T) (g := fun P => P.under (𝓞 F)) (fun P hP => Finset.mem_image_of_mem _ hP)]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[hk_lamH]`.

Use `symm`. Use `Finset.prod_subset ?_ ?_` and prove the remaining obligations. Introduce `P hP`. Rewrite `hP` using `[Finset.mem_filter]`. Rewrite using `[hk_mem_above, ← hP.2]`.

Both sides reduce to the same expression. Introduce `P hP hn`. Apply `hone` to reduce the goal to its premises. Introduce `hPT`. Apply `hn` to reduce the goal to its premises.

Rewrite using `[Finset.mem_filter]`. Conclude with `⟨hPT, HeightOneSpectrum.ext ((hk_mem_above v P).1 hP)⟩`. Rewrite using `[e]`. Conclude with `eq_inv_of_mul_eq_one_right hmain`.
-/
theorem hecke_character_product_formula : HProd := by
  classical
  intro F E _ _ _ _ _ χ S hS x
  have hfin : {P : HeightOneSpectrum (𝓞 E) | ¬ P.valuation E (x : E) = 1}.Finite := by
    have h := Filter.eventually_cofinite.1 (valued_comp_eventually E (diagUnits E x))
    simpa only [diag_comp] using h
  set T0 : Finset (HeightOneSpectrum (𝓞 E)) := S ∪ hfin.toFinset with hT0
  have hval : ∀ P, P ∉ T0 → P.valuation E (x : E) = 1 := by
    intro P hP
    by_contra h
    exact hP (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  have hone : ∀ P, P ∉ T0 → χ.locK P x = 1 := fun P hP =>
    hk_unr χ (hS P fun h => hP (Finset.mem_union_left _ h)) x (hval P hP)
  have hmain : χ.inf x * ∏ P ∈ T0, χ.locK P x = 1 := by
    have h := χ.productRule T0 (fun P hP => hS P fun h => hP (Finset.mem_union_left _ h)) x
    have h2 : (∏ᶠ (v : HeightOneSpectrum (𝓞 E)) (_ : v ∉ T0), χ.val v ^ ordF v x) = 1 := by
      refine finprod_eq_one_of_forall_eq_one fun P => ?_
      rw [finprod_eq_if]
      split_ifs with hP
      · rfl
      · have h0 : ordF P x = 0 := by
          unfold ordF
          rw [hval P hP, WithZero.log_one, neg_zero]
        rw [h0, zpow_zero]
    rw [h2, mul_one] at h
    exact h
  set T : Finset (HeightOneSpectrum (𝓞 F)) := T0.image (fun P => P.under (𝓞 F)) with hT
  have hsupp : ∀ v, v ∉ T → lamH (F := F) χ v x = 1 := by
    intro v hv
    rw [hk_lamH]
    refine Finset.prod_eq_one fun P hP => hone P fun hPT => hv ?_
    rw [hT, Finset.mem_image]
    exact ⟨P, hPT, HeightOneSpectrum.ext ((hk_mem_above v P).1 hP)⟩
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 F) => lamH (F := F) χ v x) ⊆ ↑T := by
    intro v hv
    by_contra h
    exact hv (hsupp v h)
  refine ⟨T.finite_toSet.subset hsub, ?_⟩
  rw [finprod_eq_prod_of_mulSupport_subset _ hsub]
  have e : ∏ v ∈ T, lamH (F := F) χ v x = ∏ P ∈ T0, χ.locK P x := by
    rw [← Finset.prod_fiberwise_of_maps_to (s := T0) (t := T) (g := fun P => P.under (𝓞 F)) (fun P hP => Finset.mem_image_of_mem _ hP)]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [hk_lamH]
    symm
    refine Finset.prod_subset ?_ ?_
    · intro P hP
      rw [Finset.mem_filter] at hP
      rw [hk_mem_above, ← hP.2]
      rfl
    · intro P hP hn
      apply hone
      intro hPT
      apply hn
      rw [Finset.mem_filter]
      exact ⟨hPT, HeightOneSpectrum.ext ((hk_mem_above v P).1 hP)⟩
  rw [e]
  exact eq_inv_of_mul_eq_one_right hmain

end Prod

section Inf

/- English proof (translation)
Establish `h1 : ((‖w‖ : ℝ) : ℂ) ^ 2 = w * (starRingEnd ℂ) w`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hc : (starRingEnd ℂ) w ≠ 0` using `(map_ne_zero _).2 hw`.

Rewrite using `[div_pow, h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem hk_sq (w : ℂ) (hw : w ≠ 0) : (w / ((‖w‖ : ℝ) : ℂ)) ^ 2 = w / (starRingEnd ℂ) w := by
  have h1 : ((‖w‖ : ℝ) : ℂ) ^ 2 = w * (starRingEnd ℂ) w := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    rfl
  have hc : (starRingEnd ℂ) w ≠ 0 := (map_ne_zero _).2 hw
  rw [div_pow, h1]
  field_simp

/- English proof (translation)
Introduce `X hX σ₀ χ n e hn hne x`. Rewrite using `[hn x]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Establish `hw : X.embC σ₀ τ (x : X.E) ≠ 0` using `(map_ne_zero _).2 x.ne_zero`. Rewrite using `[hne τ, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hk_sq _ hw, ← hX.conjE (X.embC σ₀ τ) (x : X.E)]`.

Use `congr 1`. Rewrite using `[map_div₀, map_div₀]`. Both sides reduce to the same expression.
-/
theorem hecke_character_infinity_type : HInf := by
  intro X hX σ₀ χ n e hn hne x
  rw [hn x]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hw : X.embC σ₀ τ (x : X.E) ≠ 0 := (map_ne_zero _).2 x.ne_zero
  rw [hne τ, zpow_mul, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, hk_sq _ hw, ← hX.conjE (X.embC σ₀ τ) (x : X.E)]
  congr 1
  rw [map_div₀, map_div₀]
  rfl

end Inf

end Formalism.L2.Ker
