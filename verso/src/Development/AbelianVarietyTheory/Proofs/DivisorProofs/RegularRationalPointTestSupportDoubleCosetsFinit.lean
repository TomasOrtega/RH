import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeparableCharpolyOfTestFunctionNeZeroRegularPlac
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdelicUnitaryPointOfLocalFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAdelicUnitaryPointEqOfSectionComponentsEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentralizStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralUnitaryConjOfCharpolyEqStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.ClsSupp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Distinguish the cases in `hsp : IsSplitAt w`. Unfold `UL`. Rewrite using `[if_pos hsp]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `GlobalTheory.LocInj.cLoc_mem_UL hsp x`.
-/
theorem cLoc_mem_UL' (w : Pl E) (x : UA E n) : cLoc w x ∈ UL n w := by
  by_cases hsp : IsSplitAt w
  · unfold UL; rw [if_pos hsp]; trivial
  · exact GlobalTheory.LocInj.cLoc_mem_UL hsp x

def cw (w : Pl E) : finU E n →* UL n w where
  toFun x := ⟨cLoc w (x : UA E n), cLoc_mem_UL' w _⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

/- English proof (translation)
The claim follows from `dif_pos (cLoc_mem_UL' w _)`.
-/
theorem toSub_eq (w : Pl E) (x : finU E n) : toSub (UL n w) (cLoc w (x : UA E n)) = cw w x :=
  dif_pos (cLoc_mem_UL' w _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem cw_val (w : Pl E) (x : finU E n) : (cw w x).1 = cLoc w (x : UA E n) := rfl

/- English proof (translation)
Introduce `w₀ hw₀ h₀`. Apply `h` to reduce the goal to its premises. Rewrite using `[finprod_mem_def]`. Use `finprod_eq_zero (S.mulIndicator g) w₀ (by rw [Set.mulIndicator_of_mem hw₀, h₀]) ?_` and prove the remaining obligations. Use `show (Function.mulSupport _).Finite`.

Rewrite using `[Set.mulSupport_mulIndicator]`. Conclude with `(Filter.eventually_cofinite.1 hg).subset Set.inter_subset_right`.
-/
theorem ne_zero_of_finprod {S : Set (Pl E)} {g : Pl E → ℂ} (hg : ∀ᶠ w in cofinite, g w = 1)
    (h : ∏ᶠ w ∈ S, g w ≠ 0) : ∀ w ∈ S, g w ≠ 0 := by
  intro w₀ hw₀ h₀
  apply h
  rw [finprod_mem_def]
  refine finprod_eq_zero (S.mulIndicator g) w₀ (by rw [Set.mulIndicator_of_mem hw₀, h₀]) ?_
  show (Function.mulSupport _).Finite
  rw [Set.mulSupport_mulIndicator]
  exact (Filter.eventually_cofinite.1 hg).subset Set.inter_subset_right

end GlobalTheory.BCT.ClsSupp

open GlobalTheory.BCT.ClsSupp in

/- English proof (translation)
Introduce `E _ _ _ hU n hn S hS K' hK' f hf γ hγ`. Use `set δ := finPt γ with hδ`. Establish `hych : ∀ w, (cw w δ).1.val.charpoly = atPl w γ.1.val.charpoly` using `fun w => by rw [cw_val, RegVan.cLoc_finPt_val, Matrix.charpoly_map]`. Establish `hysep : ∀ w, (cw w δ).1.val.charpoly.Separable` using `fun w => by rw [hych]; exact hγ.map`. Establish `hconj : ∀ (w : Pl E) (x : finU E n), cw w (x⁻¹ * δ * (MonoidHom.id (finU E n)) x) = (cw w x)⁻¹ * cw w δ * cw w x`.

Introduce `w x`. Simplify using `[map_mul, map_inv]`. Establish `hsupp : ∀ x : finU E n, globFn S f x ≠ 0 → ∀ w ∈ S, f w (cw w x) ≠ 0`. Introduce `x hx`. Use `ne_zero_of_finprod (g := fun w => f w (cw w x)) ?_ ?_` and prove the remaining obligations.

Use `filter_upwards [RegVan.eventually_toSub_mem x, hf.2] with w a b`. Rewrite `a` using `[toSub_eq]`. Rewrite using `[b, Set.indicator_of_mem a]`. Both sides reduce to the same expression. Establish `e : globFn S f x = ∏ᶠ w ∈ S, f w (cw w x)`.

Unfold `globFn`. Simplify using `only [toSub_eq]`. Rewrite using `[← e]` and apply the resulting hypothesis. Establish `hinvar : ∀ w, ∀ k ∈ K' w, ∀ z, f w (k⁻¹ * z * k) = f w z`. Introduce `w k hk z`.

Rewrite using `[mul_assoc, ((hf.1 w).2 k⁻¹ (inv_mem hk) (z * k)).1, ((hf.1 w).2 k hk z).2]`. Establish `hLfin : ∀ w, {p : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) (cw w δ) : Set (UL n w)) (K' w : Set (UL n w)) | (Quotient.out p)⁻¹ * cw w δ * Quotient.out p ∈ tsupport (f w)}.Finite` using `fun w => (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n w (cw w δ) (hysep w) (K' w) (hK'.1 w)).2 _ (hf.1 w).1.isCompact`. Establish `hloc : ∀ w (g : UL n w), f w (g⁻¹ * cw w δ * g) ≠ 0 → (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g))⁻¹ * cw w δ * Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g) ∈ tsupport (f w)`. Introduce `w g hg`. Take `⟨h, k, hh, hk, he⟩` from `DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g`.

Rewrite using `[he]`. Apply `subset_tsupport` to reduce the goal to its premises. Establish `hh' : h * cw w δ = cw w δ * h` using `hh`. Establish `e : (h * g * k)⁻¹ * cw w δ * (h * g * k) = k⁻¹ * (g⁻¹ * cw w δ * g) * k`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[hh']`. Use `group`. Use `_ = _ := by rw [inv_mul_cancel_left]`. Rewrite using `[Function.mem_support, e, hinvar w k hk]`. Conclude with `hg`.

Establish `hgood : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 → ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k` using `by filter_upwards [hf.2, hK'.2, RegVan.eventually_toSub_mem δ, GlobalTheory.T.eventually_integralUnitary_conj_of_charpoly_eq E hU n _ hγ] with w hfw hKw hyK hcK`. Introduce `g hg`. Rewrite `hg` using `[hfw]`. Establish `hz : g⁻¹ * cw w δ * g ∈ KL n w`. Assume the negation of the conclusion as `h`.

Conclude with `hg (Set.indicator_of_notMem h _)`. Rewrite `hyK` using `[toSub_eq]`. Establish `hzc : (g⁻¹ * cw w δ * g).1.val.charpoly = atPl w γ.1.val.charpoly`. Rewrite using `[Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv, Matrix.charpoly_units_conj', hych]`. Take `⟨k, hk, hke⟩` from `hcK (cw w δ) _ hyK hz (hych w) hzc`.

Use `⟨g * k⁻¹, ?_, k, by rw [hKw]; exact hk, by group⟩` and prove the remaining obligations. Use `show g * k⁻¹ * cw w δ = cw w δ * (MonoidHom.id (UL n w)) (g * k⁻¹)`. Rewrite using `[MonoidHom.id_apply]`. Combine the equalities or inequalities in the displayed calculation. Use `set B : Set (Pl E) := {w | w ∈ S ∧ ¬ ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 → ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k} with hBdef`.

Establish `hB : B.Finite` using `(Filter.eventually_cofinite.1 hgood).subset fun w hw => hw.2`. Establish `hBg : ∀ w ∈ S, w ∉ B → ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 → ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k` using `fun w hw hwB =>`. Assume the negation of the conclusion as `fun h => hwB ⟨hw, h⟩`. Use `haveI : Finite B := hB.to_subtype`. Establish `hq0 : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) δ : Set (finU E n)) (globLev S K' : Set (finU E n)), globFn S f ((Quotient.out q)⁻¹ * δ * (MonoidHom.id (finU E n)) (Quotient.out q)) ≠ 0 → ∀ w ∈ S, f w ((cw w (Quotient.out q))⁻¹ * cw w δ * cw w (Quotient.out q)) …` using `fun q hq w hw => by`.

Rewrite using `[← hconj]`. Conclude with `hsupp _ hq w hw`. Set `Φ` to `fun (q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) δ : Set (finU E n)) (globLev S K' : Set (finU E n))) (w : B) => DoubleCoset.mk (twCent (MonoidHom.id (UL n (w : Pl E))) (cw (w : Pl E) δ)) (K' w) (cw (w : Pl E) (Quotient.out q))`. Use `Set.Finite.of_finite_image (f := Φ) ?_ ?_` and prove the remaining obligations. Use `(Set.Finite.pi fun w : B => hLfin (w : Pl E)).subset ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨q, hq, rfl⟩`. Conclude with `Set.mem_univ_pi.2 fun w => hloc w _ (hq0 q hq w w.2.1)`. Introduce `q hq q' hq' he`. Establish `hloc' : ∀ w ∈ S, ∃ t ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, cw w (Quotient.out q') = t * cw w (Quotient.out q) * k`. Introduce `w hw`.

Distinguish the cases in `hwB : w ∈ B`. Conclude with `(DoubleCoset.eq _ _ _ _).1 (congrFun he ⟨w, hwB⟩)`. Take `⟨a, ha, k, hk, hak⟩` from `hBg w hw hwB _ (hq0 q hq w hw)`. Take `⟨a', ha', k', hk', hak'⟩` from `hBg w hw hwB _ (hq0 q' hq' w hw)`. Use `⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), k⁻¹ * k', mul_mem (inv_mem hk) hk', ?_⟩` and prove the remaining obligations.

Rewrite using `[hak, hak']`. Use `group`. Establish `hex : ∀ w : Pl E, ∃ t k : UL n w, t ∈ twCent (MonoidHom.id (UL n w)) (cw w δ) ∧ k ∈ K' w ∧ (w ∈ S → cw w (Quotient.out q') = t * cw w (Quotient.out q) * k) ∧ (w ∉ S → t = 1)`. Introduce `w`. Distinguish the cases in `hw : w ∈ S`.

Take `⟨t, ht, k, hk, he⟩` from `hloc' w hw`. Conclude with `⟨t, k, ht, hk, fun _ => he, fun h => absurd hw h⟩`. Conclude with `⟨1, 1, one_mem _, one_mem _, fun h => absurd h hw, fun _ => rfl⟩`. Use `choose t k ht hk hte ht1 using hex`. Establish `hKle : ∀ w, K' w ≤ KL n w` using `fun w => (hK'.1 w).2.1`.

Establish `htint : ∀ᶠ w in (cofinite : Filter (Pl E)), t w ∈ KL n w` using `by filter_upwards [RegVan.eventually_toSub_mem (Quotient.out q), RegVan.eventually_toSub_mem (Quotient.out q')] with w a b`. Rewrite `a`, `b` using `[toSub_eq]`. Distinguish the cases in `hw : w ∈ S`. Establish `e : t w = cw w (Quotient.out q') * (k w)⁻¹ * (cw w (Quotient.out q))⁻¹` using `by rw [hte w hw]; group`. Rewrite using `[e]`.

Conclude with `mul_mem (mul_mem b (inv_mem (hKle w (hk w)))) (inv_mem a)`. Rewrite using `[ht1 w hw]`. Conclude with `one_mem _`. Take `⟨tt, htt⟩` from `exists_finU_of_loc E hU n S hS t htint`. Take `⟨kk, hkk⟩` from `exists_finU_of_loc E hU n S hS k (Filter.Eventually.of_forall fun w => hKle w (hk w))`.

Simplify using `only [toSub_eq] at htt hkk`. Establish `httT : tt ∈ twCent (MonoidHom.id (finU E n)) δ` using `by show tt * δ = δ * (MonoidHom.id (finU E n)) tt`. Apply `finU_eq_of_loc E hU n S hS` to reduce the goal to its premises. Introduce `w hw`. Establish `h1 : t w * cw w δ = cw w δ * (MonoidHom.id (UL n w)) (t w)` using `ht w`.

Simplify using `only [toSub_eq, MonoidHom.id_apply, map_mul, htt w hw] at h1 ⊢`. Conclude with `h1`. Establish `hkkK : kk ∈ globLev S K'`. Simplify using `only [globLev, Subgroup.mem_iInf]`. Introduce `w hw`.

Rewrite using `[Subgroup.mem_comap]`. Conclude with `⟨k w, hk w, by rw [← hkk w hw]; rfl⟩`. Establish `hgg : Quotient.out q' = tt * Quotient.out q * kk`. Apply `finU_eq_of_loc E hU n S hS` to reduce the goal to its premises. Introduce `w hw`.

Simplify using `only [toSub_eq, map_mul, htt w hw, hkk w hw]`. Conclude with `hte w hw`. Rewrite using `[← DoubleCoset.out_eq' (twCent (MonoidHom.id (finU E n)) δ) (globLev S K') q, ← DoubleCoset.out_eq' (twCent (MonoidHom.id (finU E n)) δ) (globLev S K') q', DoubleCoset.eq]`. Conclude with `⟨tt, httT, kk, hkkK, hgg⟩`.
-/
theorem GlobalTheory.BCT.ClsSupp.finite_supp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) (finPt γ) : Set (finU E n)) (globLev S K' : Set (finU E n)) | globFn S f ((Quotient.out q)⁻¹ * finPt γ * (MonoidHom.id (finU E n)) (Quotient.out q)) ≠ 0}.Finite := by
  intro E _ _ _ hU n hn S hS K' hK' f hf γ hγ
  set δ := finPt γ with hδ
  have hych : ∀ w, (cw w δ).1.val.charpoly = atPl w γ.1.val.charpoly := fun w =>
    by rw [cw_val, RegVan.cLoc_finPt_val, Matrix.charpoly_map]
  have hysep : ∀ w, (cw w δ).1.val.charpoly.Separable := fun w => by rw [hych]; exact hγ.map
  have hconj : ∀ (w : Pl E) (x : finU E n),
      cw w (x⁻¹ * δ * (MonoidHom.id (finU E n)) x) = (cw w x)⁻¹ * cw w δ * cw w x := by
    intro w x; simp [map_mul, map_inv]

  have hsupp : ∀ x : finU E n, globFn S f x ≠ 0 → ∀ w ∈ S, f w (cw w x) ≠ 0 := by
    intro x hx
    refine ne_zero_of_finprod (g := fun w => f w (cw w x)) ?_ ?_
    · filter_upwards [RegVan.eventually_toSub_mem x, hf.2] with w a b
      rw [toSub_eq] at a
      rw [b, Set.indicator_of_mem a]; rfl
    · have e : globFn S f x = ∏ᶠ w ∈ S, f w (cw w x) := by
        unfold globFn; simp only [toSub_eq]
      rwa [← e]

  have hinvar : ∀ w, ∀ k ∈ K' w, ∀ z, f w (k⁻¹ * z * k) = f w z := by
    intro w k hk z
    rw [mul_assoc, ((hf.1 w).2 k⁻¹ (inv_mem hk) (z * k)).1, ((hf.1 w).2 k hk z).2]
  have hLfin : ∀ w, {p : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) (cw w δ) : Set (UL n w)) (K' w : Set (UL n w)) |
      (Quotient.out p)⁻¹ * cw w δ * Quotient.out p ∈ tsupport (f w)}.Finite := fun w =>
    (GlobalTheory.T.unitary_local_finiteness_regular_semisimple_centralizer E hU n w (cw w δ) (hysep w) (K' w) (hK'.1 w)).2 _ (hf.1 w).1.isCompact
  have hloc : ∀ w (g : UL n w), f w (g⁻¹ * cw w δ * g) ≠ 0 →
      (Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g))⁻¹ * cw w δ *
        Quotient.out (DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g) ∈ tsupport (f w) := by
    intro w g hg
    obtain ⟨h, k, hh, hk, he⟩ := DoubleCoset.mk_out_eq_mul (twCent (MonoidHom.id (UL n w)) (cw w δ)) (K' w) g
    rw [he]
    apply subset_tsupport
    have hh' : h * cw w δ = cw w δ * h := hh
    have e : (h * g * k)⁻¹ * cw w δ * (h * g * k) = k⁻¹ * (g⁻¹ * cw w δ * g) * k := by
      calc (h * g * k)⁻¹ * cw w δ * (h * g * k) = k⁻¹ * (g⁻¹ * (h⁻¹ * (h * cw w δ)) * g) * k := by
            rw [hh']; group
        _ = _ := by rw [inv_mul_cancel_left]
    rw [Function.mem_support, e, hinvar w k hk]; exact hg

  have hgood : ∀ᶠ w in (cofinite : Filter (Pl E)), ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 →
      ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k := by
    filter_upwards [hf.2, hK'.2, RegVan.eventually_toSub_mem δ, GlobalTheory.T.eventually_integralUnitary_conj_of_charpoly_eq E hU n _ hγ] with w hfw hKw hyK hcK
    intro g hg
    rw [hfw] at hg
    have hz : g⁻¹ * cw w δ * g ∈ KL n w := by
      by_contra h; exact hg (Set.indicator_of_notMem h _)
    rw [toSub_eq] at hyK
    have hzc : (g⁻¹ * cw w δ * g).1.val.charpoly = atPl w γ.1.val.charpoly := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
        Matrix.charpoly_units_conj', hych]
    obtain ⟨k, hk, hke⟩ := hcK (cw w δ) _ hyK hz (hych w) hzc
    refine ⟨g * k⁻¹, ?_, k, by rw [hKw]; exact hk, by group⟩
    show g * k⁻¹ * cw w δ = cw w δ * (MonoidHom.id (UL n w)) (g * k⁻¹)
    rw [MonoidHom.id_apply]
    calc g * k⁻¹ * cw w δ = g * (k⁻¹ * cw w δ * k) * k⁻¹ := by group
      _ = g * (g⁻¹ * cw w δ * g) * k⁻¹ := by rw [hke]
      _ = cw w δ * (g * k⁻¹) := by group
  set B : Set (Pl E) := {w | w ∈ S ∧ ¬ ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 →
      ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k} with hBdef
  have hB : B.Finite := (Filter.eventually_cofinite.1 hgood).subset fun w hw => hw.2
  have hBg : ∀ w ∈ S, w ∉ B → ∀ g : UL n w, f w (g⁻¹ * cw w δ * g) ≠ 0 →
      ∃ a ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w, g = a * k := fun w hw hwB =>
    by_contra fun h => hwB ⟨hw, h⟩
  haveI : Finite B := hB.to_subtype
  have hq0 : ∀ q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) δ : Set (finU E n)) (globLev S K' : Set (finU E n)),
      globFn S f ((Quotient.out q)⁻¹ * δ * (MonoidHom.id (finU E n)) (Quotient.out q)) ≠ 0 → ∀ w ∈ S,
      f w ((cw w (Quotient.out q))⁻¹ * cw w δ * cw w (Quotient.out q)) ≠ 0 := fun q hq w hw => by
    rw [← hconj]; exact hsupp _ hq w hw
  let Φ := fun (q : DoubleCoset.Quotient (twCent (MonoidHom.id (finU E n)) δ : Set (finU E n)) (globLev S K' : Set (finU E n)))
      (w : B) => DoubleCoset.mk (twCent (MonoidHom.id (UL n (w : Pl E))) (cw (w : Pl E) δ)) (K' w) (cw (w : Pl E) (Quotient.out q))
  refine Set.Finite.of_finite_image (f := Φ) ?_ ?_
  · refine (Set.Finite.pi fun w : B => hLfin (w : Pl E)).subset ?_
    rintro _ ⟨q, hq, rfl⟩
    exact Set.mem_univ_pi.2 fun w => hloc w _ (hq0 q hq w w.2.1)
  · intro q hq q' hq' he
    have hloc' : ∀ w ∈ S, ∃ t ∈ twCent (MonoidHom.id (UL n w)) (cw w δ), ∃ k ∈ K' w,
        cw w (Quotient.out q') = t * cw w (Quotient.out q) * k := by
      intro w hw
      by_cases hwB : w ∈ B
      · exact (DoubleCoset.eq _ _ _ _).1 (congrFun he ⟨w, hwB⟩)
      · obtain ⟨a, ha, k, hk, hak⟩ := hBg w hw hwB _ (hq0 q hq w hw)
        obtain ⟨a', ha', k', hk', hak'⟩ := hBg w hw hwB _ (hq0 q' hq' w hw)
        refine ⟨a' * a⁻¹, mul_mem ha' (inv_mem ha), k⁻¹ * k', mul_mem (inv_mem hk) hk', ?_⟩
        rw [hak, hak']; group
    have hex : ∀ w : Pl E, ∃ t k : UL n w, t ∈ twCent (MonoidHom.id (UL n w)) (cw w δ) ∧ k ∈ K' w ∧
        (w ∈ S → cw w (Quotient.out q') = t * cw w (Quotient.out q) * k) ∧ (w ∉ S → t = 1) := by
      intro w
      by_cases hw : w ∈ S
      · obtain ⟨t, ht, k, hk, he⟩ := hloc' w hw
        exact ⟨t, k, ht, hk, fun _ => he, fun h => absurd hw h⟩
      · exact ⟨1, 1, one_mem _, one_mem _, fun h => absurd h hw, fun _ => rfl⟩
    choose t k ht hk hte ht1 using hex
    have hKle : ∀ w, K' w ≤ KL n w := fun w => (hK'.1 w).2.1
    have htint : ∀ᶠ w in (cofinite : Filter (Pl E)), t w ∈ KL n w := by
      filter_upwards [RegVan.eventually_toSub_mem (Quotient.out q), RegVan.eventually_toSub_mem (Quotient.out q')]
        with w a b
      rw [toSub_eq] at a b
      by_cases hw : w ∈ S
      · have e : t w = cw w (Quotient.out q') * (k w)⁻¹ * (cw w (Quotient.out q))⁻¹ := by rw [hte w hw]; group
        rw [e]; exact mul_mem (mul_mem b (inv_mem (hKle w (hk w)))) (inv_mem a)
      · rw [ht1 w hw]; exact one_mem _
    obtain ⟨tt, htt⟩ := exists_finU_of_loc E hU n S hS t htint
    obtain ⟨kk, hkk⟩ := exists_finU_of_loc E hU n S hS k (Filter.Eventually.of_forall fun w => hKle w (hk w))
    simp only [toSub_eq] at htt hkk
    have httT : tt ∈ twCent (MonoidHom.id (finU E n)) δ := by
      show tt * δ = δ * (MonoidHom.id (finU E n)) tt
      apply finU_eq_of_loc E hU n S hS
      intro w hw
      have h1 : t w * cw w δ = cw w δ * (MonoidHom.id (UL n w)) (t w) := ht w
      simp only [toSub_eq, MonoidHom.id_apply, map_mul, htt w hw] at h1 ⊢
      exact h1
    have hkkK : kk ∈ globLev S K' := by
      simp only [globLev, Subgroup.mem_iInf]
      intro w hw
      rw [Subgroup.mem_comap]
      exact ⟨k w, hk w, by rw [← hkk w hw]; rfl⟩
    have hgg : Quotient.out q' = tt * Quotient.out q * kk := by
      apply finU_eq_of_loc E hU n S hS
      intro w hw
      simp only [toSub_eq, map_mul, htt w hw, hkk w hw]
      exact hte w hw
    rw [← DoubleCoset.out_eq' (twCent (MonoidHom.id (finU E n)) δ) (globLev S K') q,
      ← DoubleCoset.out_eq' (twCent (MonoidHom.id (finU E n)) δ) (globLev S K') q', DoubleCoset.eq]
    exact ⟨tt, httT, kk, hkkK, hgg⟩
